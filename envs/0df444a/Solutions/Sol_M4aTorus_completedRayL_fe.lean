-- Prove2me | solution 1 for M4aTorus.completedRayL_fe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4ebaf928-a587-5f43-88f7-3645bf41976f

import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_NumberField_EuclideanIdealLattice
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.IntegralDomain
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Definitions.Def_NarrowRayClassGroup
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_FrobeniusDensity_ClassGroupLSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aTorus_completedRayL_fe

section TcFold_M4aTheta_ClassSum

open Real NumberField Module
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

private def classCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ //
    ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) = n}

private def idealClass (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ClassGroup (𝓞 K) :=
  ClassGroup.mk K I

end Deep.Analytic

end

end TcFold_M4aTheta_ClassSum

section TcFold_M4aTheta_PiGaussian

open Real Set MeasureTheory Filter
open scoped Real Topology FourierTransform RealInnerProductSpace
p2m_open "Complex~exp~continuous_exp"

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {ι : Type*} [Fintype ι]

end Deep.Analytic

end

end TcFold_M4aTheta_PiGaussian

section TcFold_M4aTheta_MixedTransport

open Real MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

open scoped Classical

variable (K : Type) [Field K] [NumberField K]

private def twoConjEquiv : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := 2 * (starRingEnd ℂ) z
  invFun z := (starRingEnd ℂ) z / 2
  map_add' z w := by simp; ring
  map_smul' r z := by
    simp only [RingHom.id_apply, starRingEnd_apply, star_smul, star_trivial,
      mul_smul_comm]
  left_inv z := by simp [map_mul, map_ofNat]
  right_inv z := by simp [map_div₀, map_ofNat]; ring

private def mixedConjDil : (euclidean.mixedSpace K) ≃ₗ[ℝ] (euclidean.mixedSpace K) :=
  (WithLp.linearEquiv 2 ℝ _).trans <|
    (((LinearEquiv.refl ℝ (EuclideanSpace ℝ {w : InfinitePlace K // IsReal w})).prodCongr
      ((WithLp.linearEquiv 2 ℝ ({w : InfinitePlace K // IsComplex w} → ℂ)).trans <|
        (LinearEquiv.piCongrRight fun _ : {w : InfinitePlace K // IsComplex w} =>
          twoConjEquiv).trans
          (WithLp.linearEquiv 2 ℝ
            ({w : InfinitePlace K // IsComplex w} → ℂ)).symm)).trans
      (WithLp.linearEquiv 2 ℝ _).symm)

private theorem mixedConjDil_apply_fst (x : euclidean.mixedSpace K) :
    (mixedConjDil K x).fst = x.fst := by
  simp [mixedConjDil, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

private theorem mixedConjDil_apply_snd (x : euclidean.mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (mixedConjDil K x).snd w = 2 * (starRingEnd ℂ) (x.snd w) := by
  simp [mixedConjDil, twoConjEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.piCongrRight_apply]

private theorem euclideanRepr_inl (x : euclidean.mixedSpace K)
    (v : {w : InfinitePlace K // IsReal w}) :
    (euclidean.stdOrthonormalBasis K).repr x (Sum.inl v) = x.fst v := by
  rw [OrthonormalBasis.repr_apply_apply]
  simp [euclidean.stdOrthonormalBasis, WithLp.prod_inner_apply]
  simpa [EuclideanSpace.basisFun_apply] using
    EuclideanSpace.basisFun_inner (x := WithLp.fst x) (i := v)

private theorem euclideanRepr_inr_re (x : euclidean.mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (euclidean.stdOrthonormalBasis K).repr x (Sum.inr (w, 0)) = (x.snd w).re := by
  classical
  rw [OrthonormalBasis.repr_apply_apply]
  simp [euclidean.stdOrthonormalBasis, WithLp.prod_inner_apply,
    Pi.orthonormalBasis_apply,
    PiLp.inner_apply, PiLp.single_apply, Complex.coe_orthonormalBasisOneI,
    apply_ite Complex.re, Finset.sum_ite_eq']

private theorem euclideanRepr_inr_im (x : euclidean.mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (euclidean.stdOrthonormalBasis K).repr x (Sum.inr (w, 1)) = (x.snd w).im := by
  classical
  rw [OrthonormalBasis.repr_apply_apply]
  simp [euclidean.stdOrthonormalBasis, WithLp.prod_inner_apply,
    Pi.orthonormalBasis_apply,
    PiLp.inner_apply, PiLp.single_apply, Complex.coe_orthonormalBasisOneI,
    apply_ite Complex.re, apply_ite Complex.im, Complex.I_re,
    Finset.sum_ite_eq']

private theorem sum_sq_euclideanRepr (x : euclidean.mixedSpace K) :
    ∑ i : index K, ((euclidean.stdOrthonormalBasis K).repr x i) ^ 2 = ‖x‖ ^ 2 := by
  have hn : ‖(euclidean.stdOrthonormalBasis K).repr x‖ = ‖x‖ :=
    (euclidean.stdOrthonormalBasis K).repr.norm_map x
  rw [← hn, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

end Deep.Analytic
end

end TcFold_M4aTheta_MixedTransport

section TcFold_M4aTheta_PlaceTrace

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

p2m_open "Real MeasureTheory Set Function Topology Filter Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Finset Set.Finset"

open scoped Classical ComplexConjugate RealInnerProductSpace

variable (K : Type) [Field K] [NumberField K]

private theorem mkFiber_of_isReal {w : InfinitePlace K} (hw : IsReal w) :
    ({φ : K →+* ℂ | InfinitePlace.mk φ = w} : Finset _) = {w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    rcases mk_eq_iff.mp (h.trans (mk_embedding w).symm) with h' | h'
    · exact h'
    · rw [← conjugate_embedding_eq_of_isReal hw, ← h']
      exact (star_star φ).symm
  · rintro rfl
    exact mk_embedding w

private theorem mkFiber_eq_pair (w : InfinitePlace K) :
    ({φ : K →+* ℂ | InfinitePlace.mk φ = w} : Finset _)
      = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    rcases mk_eq_iff.mp (h.trans (mk_embedding w).symm) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by rw [← h']; exact (star_star φ).symm)
  · rintro (rfl | rfl)
    · exact mk_embedding w
    · rw [mk_conjugate_eq, mk_embedding]

private theorem embedding_ne_conjugate_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have : ComplexEmbedding.IsReal w.embedding := by
    rw [ComplexEmbedding.isReal_iff]; exact h.symm
  exact (not_isReal_iff_isComplex.mpr hw) (isReal_iff.mpr this)

private theorem sum_embeddings_eq_sum_infinitePlace {M : Type} [AddCommMonoid M]
    (f : (K →+* ℂ) → M) :
    ∑ φ : K →+* ℂ, f φ
      = (∑ w : {w : InfinitePlace K // IsReal w}, f w.1.embedding)
        + ∑ w : {w : InfinitePlace K // IsComplex w},
            (f w.1.embedding + f (ComplexEmbedding.conjugate w.1.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f,
    sum_eq_sum_add_sum
      (fun w => ∑ φ ∈ ({φ : K →+* ℂ | InfinitePlace.mk φ = w} : Finset _), f φ)]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mkFiber_of_isReal K w.2, Finset.sum_singleton]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mkFiber_eq_pair K w.1,
      Finset.sum_pair (embedding_ne_conjugate_of_isComplex K w.2)]

private theorem trace_eq_sum_infinitePlace (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ)
      = (∑ w : {w : InfinitePlace K // IsReal w}, w.1.embedding x)
        + ∑ w : {w : InfinitePlace K // IsComplex w},
            (w.1.embedding x + conj (w.1.embedding x)) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := x)
  rw [show (algebraMap ℚ ℂ) (Algebra.trace ℚ K x)
      = ((Algebra.trace ℚ K x : ℚ) : ℂ) from rfl] at h
  rw [h, ← Equiv.sum_comp (RingHom.equivRatAlgHom K ℂ) (fun σ : K →ₐ[ℚ] ℂ => σ x)]
  have hco : ∀ φ : K →+* ℂ, (RingHom.equivRatAlgHom K ℂ φ) x = φ x := fun _ => rfl
  simp_rw [hco]
  rw [sum_embeddings_eq_sum_infinitePlace K (fun φ => φ x)]
  simp_rw [ComplexEmbedding.conjugate_coe_eq]

private theorem trace_eq_sum_infinitePlace_real (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℝ)
      = (∑ w : {w : InfinitePlace K // IsReal w},
            embedding_of_isReal w.2 x)
        + ∑ w : {w : InfinitePlace K // IsComplex w},
            2 * (w.1.embedding x).re := by
  have h := trace_eq_sum_infinitePlace K x
  have hreal : ∀ w : {w : InfinitePlace K // IsReal w},
      (w.1.embedding x : ℂ) = ((embedding_of_isReal w.2 x : ℝ) : ℂ) :=
    fun w => (embedding_of_isReal_apply w.2 x).symm
  have hpair : ∀ w : {w : InfinitePlace K // IsComplex w},
      w.1.embedding x + conj (w.1.embedding x)
        = ((2 * (w.1.embedding x).re : ℝ) : ℂ) := fun w =>
    Complex.add_conj _
  rw [Finset.sum_congr rfl (fun w _ => hreal w),
    Finset.sum_congr rfl (fun w _ => hpair w), ← Complex.ofReal_sum,
    ← Complex.ofReal_sum, ← Complex.ofReal_add] at h
  exact_mod_cast h

private theorem toMixed_symm_fst (v : mixedSpace K)
    (w : {w : InfinitePlace K // IsReal w}) :
    ((euclidean.toMixed K).symm v).fst w = v.1 w := rfl

private theorem toMixed_symm_snd (v : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    ((euclidean.toMixed K).symm v).snd w = v.2 w := rfl

private theorem toMixed_symm_mixedEmbedding_fst (x : K) (w : {w : InfinitePlace K // IsReal w}) :
    ((euclidean.toMixed K).symm (mixedEmbedding K x)).fst w
      = embedding_of_isReal w.2 x := by
  rw [toMixed_symm_fst, mixedEmbedding_apply_isReal]

private theorem toMixed_symm_mixedEmbedding_snd (x : K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    ((euclidean.toMixed K).symm (mixedEmbedding K x)).snd w
      = w.1.embedding x := by
  rw [toMixed_symm_snd, mixedEmbedding_apply_isComplex]

private theorem euclidean_inner_apply (x y : euclidean.mixedSpace K) :
    inner ℝ x y
      = (∑ w : {w : InfinitePlace K // IsReal w}, x.fst w * y.fst w)
        + ∑ w : {w : InfinitePlace K // IsComplex w},
            (y.snd w * conj (x.snd w)).re := by
  rw [WithLp.prod_inner_apply, PiLp.inner_apply, PiLp.inner_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by
      show (WithLp.fst y).ofLp w * (starRingEnd ℝ) ((WithLp.fst x).ofLp w)
        = (WithLp.fst x).ofLp w * (WithLp.fst y).ofLp w
      rw [conj_trivial, mul_comm]

private theorem inner_mixedConjDil_eq_trace (x y : K) :
    inner ℝ ((euclidean.toMixed K).symm (mixedEmbedding K x))
      (mixedConjDil K ((euclidean.toMixed K).symm (mixedEmbedding K y)))
      = ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) := by
  rw [euclidean_inner_apply, trace_eq_sum_infinitePlace_real]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedConjDil_apply_fst, toMixed_symm_mixedEmbedding_fst, toMixed_symm_mixedEmbedding_fst,
      ← map_mul]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedConjDil_apply_snd, toMixed_symm_mixedEmbedding_snd, toMixed_symm_mixedEmbedding_snd,
      map_mul]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring

end Deep.Analytic

end

end TcFold_M4aTheta_PlaceTrace

section TcFold_M4aTheta_PiPoisson

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Real MeasureTheory Set Function Topology
open TopologicalSpace (Compacts)
open scoped ComplexConjugate

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {d : Type} [Fintype d]

private def intVec (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

private def toTorus (x : d → ℝ) : UnitAddTorus d := fun i => ((x i : ℝ) : AddCircle (1 : ℝ))

private theorem isOpenQuotientMap_toTorus : IsOpenQuotientMap (toTorus (d := d)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

private theorem toTorus_surjective : Function.Surjective (toTorus (d := d)) :=
  isOpenQuotientMap_toTorus.surjective

private theorem toTorus_continuous : Continuous (toTorus (d := d)) :=
  isOpenQuotientMap_toTorus.continuous

private theorem toTorus_add_intVec (x : d → ℝ) (n : d → ℤ) :
    toTorus (x + intVec n) = toTorus x := by
  funext i
  show ((x i + (n i : ℝ) : ℝ) : AddCircle (1 : ℝ)) = ((x i : ℝ) : AddCircle (1 : ℝ))
  have h0 : (((n i : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n i, by simp⟩
  rw [show ((x i + (n i : ℝ) : ℝ) : AddCircle (1 : ℝ))
        = ((x i : ℝ) : AddCircle (1 : ℝ)) + (((n i : ℝ)) : AddCircle (1 : ℝ)) from rfl,
    h0, add_zero]

private theorem exists_intVec_of_toTorus_eq {a b : d → ℝ} (h : toTorus a = toTorus b) :
    ∃ k : d → ℤ, a = b + intVec k := by
  have hmem : ∀ i, ∃ k : ℤ, k • (1 : ℝ) = a i - b i := by
    intro i
    have hi : ((a i : ℝ) : AddCircle (1 : ℝ)) = ((b i : ℝ) : AddCircle (1 : ℝ)) :=
      congrFun h i
    have := (QuotientAddGroup.eq_iff_sub_mem).mp hi
    exact AddSubgroup.mem_zmultiples_iff.mp this
  choose k hk using hmem
  refine ⟨k, ?_⟩
  funext i
  have hki := hk i
  simp only [zsmul_eq_mul, mul_one] at hki
  show a i = b i + (k i : ℝ)
  linarith [hki]

private theorem norm_mFourier_apply (n : d → ℤ) (x : UnitAddTorus d) :
    ‖UnitAddTorus.mFourier n x‖ = 1 := by
  rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [fourier_apply]
  exact (AddCircle.toCircle _).norm_coe

section PortCore

variable (f : C((d → ℝ), ℂ))

private def translate (n : d → ℤ) : C((d → ℝ), ℂ) :=
  f.comp (ContinuousMap.addRight (intVec n))

private theorem translate_apply (n : d → ℤ) (x : d → ℝ) :
    translate f n x = f (x + intVec n) := rfl

variable {f}
variable (h_norm : ∀ K : Compacts (d → ℝ),
    Summable fun n : d → ℤ => ‖(translate f n).restrict K‖)

include h_norm

private theorem translate_summable : Summable (translate f) :=
  ContinuousMap.summable_of_locally_summable_norm h_norm

private theorem tsum_translate_apply (x : d → ℝ) :
    (∑' n : d → ℤ, translate f n) x = ∑' n : d → ℤ, f (x + intVec n) := by
  rw [← ContinuousMap.tsum_apply (translate_summable h_norm)]
  exact tsum_congr fun n => rfl

private theorem tsum_translate_periodic (k : d → ℤ) (x : d → ℝ) :
    (∑' n : d → ℤ, translate f n) (x + intVec k)
      = (∑' n : d → ℤ, translate f n) x := by
  rw [tsum_translate_apply h_norm, tsum_translate_apply h_norm]
  have hre : ∀ n : d → ℤ, x + intVec k + intVec n = x + intVec (k + n) := by
    intro n; funext i
    show x i + (k i : ℝ) + (n i : ℝ) = x i + ((k + n) i : ℝ)
    push_cast [Pi.add_apply]
    ring
  calc ∑' n : d → ℤ, f (x + intVec k + intVec n)
      = ∑' n : d → ℤ, f (x + intVec (k + n)) := by
        exact tsum_congr fun n => by rw [hre n]
    _ = ∑' n : d → ℤ, f (x + intVec n) := by
        exact ((Equiv.addLeft k).tsum_eq fun n => f (x + intVec n))

private theorem tsum_translate_fiberwise {a b : d → ℝ} (hab : toTorus a = toTorus b) :
    (∑' n : d → ℤ, translate f n) a = (∑' n : d → ℤ, translate f n) b := by
  obtain ⟨k, rfl⟩ := exists_intVec_of_toTorus_eq hab
  exact tsum_translate_periodic h_norm k b

private def periodization : C(UnitAddTorus d, ℂ) where
  toFun := fun y =>
    (∑' n : d → ℤ, translate f n) (Function.surjInv toTorus_surjective y)
  continuous_toFun := by
    rw [← isOpenQuotientMap_toTorus.continuous_comp_iff]
    have hcomp : (fun y =>
        (∑' n : d → ℤ, translate f n) (Function.surjInv toTorus_surjective y))
          ∘ toTorus
        = ⇑(∑' n : d → ℤ, translate f n) := by
      funext x
      exact tsum_translate_fiberwise h_norm
        (Function.surjInv_eq toTorus_surjective (toTorus x))
    rw [hcomp]
    exact map_continuous _

private theorem periodization_toTorus (x : d → ℝ) :
    periodization h_norm (toTorus x) = ∑' n : d → ℤ, f (x + intVec n) := by
  rw [← tsum_translate_apply h_norm]
  exact tsum_translate_fiberwise h_norm
    (Function.surjInv_eq toTorus_surjective (toTorus x))

end PortCore

private def piFourier (f : (d → ℝ) → ℂ) (m : d → ℤ) : ℂ :=
  ∫ x : d → ℝ, UnitAddTorus.mFourier (-m) (toTorus x) * f x

section Tiles

private def unitCube : Set (d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

private def cubeTile (n : d → ℤ) : Set (d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc ((n i : ℝ)) ((n i : ℝ) + 1)}

private theorem unitCube_eq_pi : unitCube (d := d) = Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1 := by
  ext x; simp [unitCube, Set.mem_pi]

private theorem cubeTile_eq_pi (n : d → ℤ) :
    cubeTile n = Set.pi Set.univ fun i => Set.Ioc ((n i : ℝ)) ((n i : ℝ) + 1) := by
  ext x; simp [cubeTile, Set.mem_pi]

private theorem measurableSet_unitCube : MeasurableSet (unitCube (d := d)) := by
  rw [unitCube_eq_pi]
  exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioc

private theorem measurableSet_cubeTile (n : d → ℤ) : MeasurableSet (cubeTile n) := by
  rw [cubeTile_eq_pi]
  exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioc

private theorem volume_unitCube : volume (unitCube (d := d)) = 1 := by
  rw [unitCube_eq_pi, volume_pi_pi]
  simp [Real.volume_Ioc]

private theorem cubeTile_preimage (n : d → ℤ) :
    (fun x : d → ℝ => x + intVec n) ⁻¹' cubeTile n = unitCube (d := d) := by
  ext x
  simp only [Set.mem_preimage, cubeTile, unitCube, Set.mem_setOf_eq, Pi.add_apply,
    Set.mem_Ioc, intVec]
  exact forall_congr' fun i => by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

private theorem cubeTile_disjoint : Pairwise (Function.onFun Disjoint (cubeTile (d := d))) := by
  intro n m hnm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hnm
  refine Set.disjoint_left.mpr fun x hxn hxm => ?_
  have h1 := hxn i; have h2 := hxm i
  simp only [Set.mem_Ioc] at h1 h2
  rcases lt_or_gt_of_ne hi with h | h
  · have : (n i : ℝ) + 1 ≤ (m i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith [h1.2, h2.1]
  · have : (m i : ℝ) + 1 ≤ (n i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith [h1.1, h2.2]

private theorem iUnion_cubeTile : (⋃ n : d → ℤ, cubeTile n) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨fun i => ⌈x i⌉ - 1, fun i => ?_⟩
  have h1 : ((⌈x i⌉ - 1 : ℤ) : ℝ) = (⌈x i⌉ : ℝ) - 1 := by push_cast; ring
  constructor
  · rw [h1]; linarith [Int.ceil_lt_add_one (x i)]
  · rw [h1]; linarith [Int.le_ceil (x i)]

end Tiles

section Coefficient

variable {f : C((d → ℝ), ℂ)}
variable (h_norm : ∀ K : Compacts (d → ℝ),
    Summable fun n : d → ℤ => ‖(translate f n).restrict K‖)

private def unitCubeCompacts : Compacts (d → ℝ) :=
  ⟨Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
    isCompact_univ_pi fun _ => isCompact_Icc⟩

private theorem unitCube_subset_compacts : unitCube (d := d) ⊆ (unitCubeCompacts (d := d) : Set (d → ℝ)) := by
  intro x hx i _
  exact Set.Ioc_subset_Icc_self (hx i)

private theorem norm_le_restrict_on_unitCube (n : d → ℤ) {x : d → ℝ} (hx : x ∈ unitCube (d := d)) :
    ‖f (x + intVec n)‖ ≤ ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
  have := ContinuousMap.norm_coe_le_norm ((translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ)))
    ⟨x, unitCube_subset_compacts hx⟩
  exact this

include h_norm

private theorem integrable_of_summable_translate_norm : Integrable (⇑f) := by
  haveI : (volume : Measure (d → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi d
  refine ⟨(map_continuous f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hsplit : ∫⁻ x, ‖f x‖ₑ
      = ∑' n : d → ℤ, ∫⁻ x in cubeTile n, ‖f x‖ₑ := by
    rw [← lintegral_iUnion measurableSet_cubeTile cubeTile_disjoint (fun x => ‖f x‖ₑ)]
    rw [iUnion_cubeTile, Measure.restrict_univ]
  have htile : ∀ n : d → ℤ, ∫⁻ x in cubeTile n, ‖f x‖ₑ
      = ∫⁻ x in unitCube, ‖f (x + intVec n)‖ₑ := by
    intro n
    have hmp : MeasurePreserving (fun x : d → ℝ => x + intVec n) volume volume :=
      measurePreserving_add_right volume (intVec n)
    rw [← hmp.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.addRight (intVec n)).measurableEmbedding, cubeTile_preimage]
  have hbound : ∀ n : d → ℤ, ∫⁻ x in unitCube, ‖f (x + intVec n)‖ₑ
      ≤ ENNReal.ofReal ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
    intro n
    calc ∫⁻ x in unitCube, ‖f (x + intVec n)‖ₑ
        ≤ ∫⁻ _ in unitCube, ENNReal.ofReal ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_unitCube] with x hx
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_le_restrict_on_unitCube n hx)
      _ = ENNReal.ofReal ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
          rw [setLIntegral_const, volume_unitCube, mul_one]
  rw [hsplit]
  calc ∑' n : d → ℤ, ∫⁻ x in cubeTile n, ‖f x‖ₑ
      ≤ ∑' n : d → ℤ, ENNReal.ofReal ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [htile n]; exact hbound n
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (h_norm unitCubeCompacts)]
        exact ENNReal.ofReal_lt_top

private theorem mFourierCoeff_periodization (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(periodization h_norm)) m = piFourier (⇑f) m := by
  haveI : (volume : Measure (d → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi d
  have hS0 : {x : d → ℝ | ∀ i, x i ∈ Set.Ioc ((fun _ => (0:ℝ)) i) ((fun _ => (0:ℝ)) i + 1)}
      = unitCube (d := d) := by
    ext x; simp [unitCube]

  have hrep : ∀ x : d → ℝ, UnitAddTorus.mFourier (-m) (fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
      • periodization h_norm (fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
      = ∑' n : d → ℤ, UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n) := by
    intro x
    have : (fun i => ((x i : ℝ) : AddCircle (1:ℝ))) = toTorus x := rfl
    rw [this, smul_eq_mul, periodization_toTorus h_norm, ← tsum_mul_left]

  have hInt : ∀ n : d → ℤ, IntegrableOn
      (fun x => UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n)) unitCube := by
    intro n
    have hc : Continuous fun x : d → ℝ =>
        UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n) := by
      exact ((map_continuous _).comp toTorus_continuous).mul
        ((map_continuous f).comp (continuous_id.add continuous_const))
    exact ((hc.continuousOn).integrableOn_compact unitCubeCompacts.2).mono_set unitCube_subset_compacts

  have hNorm : Summable fun n : d → ℤ =>
      ∫ x in unitCube, ‖UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n)‖ := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _) (fun n => ?_) (h_norm unitCubeCompacts)
    have hle : ∀ x ∈ unitCube (d := d),
        ‖UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n)‖
          ≤ ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
      intro x hx
      rw [norm_mul, norm_mFourier_apply, one_mul]
      exact norm_le_restrict_on_unitCube n hx
    calc ∫ x in unitCube, ‖UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n)‖
        ≤ ∫ _ in unitCube, ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
          refine setIntegral_mono_on ((hInt n).norm) ?_ measurableSet_unitCube hle
          exact integrableOn_const (by rw [volume_unitCube]; exact ENNReal.one_ne_top)
      _ = ‖(translate f n).restrict (unitCubeCompacts : Compacts (d → ℝ))‖ := by
          rw [setIntegral_const]
          have h1 : volume.real (unitCube (d := d)) = 1 := by
            simp [measureReal_def, volume_unitCube]
          rw [h1, one_smul]

  rw [UnitAddTorus.mFourierCoeff_eq_integral (⇑(periodization h_norm)) m (fun _ => 0)]
  calc ∫ x in {x : d → ℝ | ∀ i, x i ∈ Set.Ioc ((fun _ => (0:ℝ)) i) ((fun _ => (0:ℝ)) i + 1)},
        UnitAddTorus.mFourier (-m) (fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
          • periodization h_norm (fun i => ((x i : ℝ) : AddCircle (1:ℝ)))
      = ∫ x in unitCube,
          ∑' n : d → ℤ, UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n) := by
        rw [hS0]
        exact setIntegral_congr_fun measurableSet_unitCube fun x _ => hrep x
    _ = ∑' n : d → ℤ, ∫ x in unitCube,
          UnitAddTorus.mFourier (-m) (toTorus x) * f (x + intVec n) := by
        exact (integral_tsum_of_summable_integral_norm hInt hNorm).symm
    _ = ∑' n : d → ℤ, ∫ x in cubeTile n,
          UnitAddTorus.mFourier (-m) (toTorus x) * f x := by
        refine tsum_congr fun n => ?_
        have hmp : MeasurePreserving (fun x : d → ℝ => x + intVec n) volume volume :=
          measurePreserving_add_right volume (intVec n)
        rw [← hmp.setIntegral_preimage_emb
          (MeasurableEquiv.addRight (intVec n)).measurableEmbedding
          (fun x => UnitAddTorus.mFourier (-m) (toTorus x) * f x) (cubeTile n),
          cubeTile_preimage]
        refine setIntegral_congr_fun measurableSet_unitCube fun x _ => ?_
        rw [toTorus_add_intVec]
    _ = ∫ x, UnitAddTorus.mFourier (-m) (toTorus x) * f x := by
        have hint : Integrable fun x : d → ℝ =>
            UnitAddTorus.mFourier (-m) (toTorus x) * f x := by
          refine (integrable_of_summable_translate_norm h_norm).bdd_mul (c := 1)
            ((map_continuous _).comp toTorus_continuous).aestronglyMeasurable ?_
          filter_upwards with x
          rw [norm_mFourier_apply]
        have hiu : (⋃ n : d → ℤ, cubeTile n) = Set.univ := iUnion_cubeTile
        have hion : IntegrableOn
            (fun x => UnitAddTorus.mFourier (-m) (toTorus x) * f x)
            (⋃ n : d → ℤ, cubeTile n) := by
          rw [hiu]; exact hint.integrableOn
        have hhs := hasSum_integral_iUnion measurableSet_cubeTile cubeTile_disjoint hion
        have h2 := hhs.tsum_eq
        rw [hiu, Measure.restrict_univ] at h2
        exact h2
    _ = piFourier (⇑f) m := rfl

private theorem tsum_eq_tsum_piFourier
    (h_sum : Summable fun m : d → ℤ => piFourier (⇑f) m) (x : d → ℝ) :
    ∑' n : d → ℤ, f (x + intVec n)
      = ∑' m : d → ℤ, piFourier (⇑f) m * UnitAddTorus.mFourier m (toTorus x) := by
  have hcoeff : Summable (UnitAddTorus.mFourierCoeff (⇑(periodization h_norm))) :=
    h_sum.congr fun m => (mFourierCoeff_periodization h_norm m).symm
  have hps := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hcoeff (toTorus x)
  rw [← periodization_toTorus h_norm]
  refine (hps.congr_fun fun m => ?_).tsum_eq.symm
  rw [mFourierCoeff_periodization h_norm m, smul_eq_mul]

private theorem tsum_intVec_eq_tsum_piFourier
    (h_sum : Summable fun m : d → ℤ => piFourier (⇑f) m) :
    ∑' n : d → ℤ, f (intVec n) = ∑' m : d → ℤ, piFourier (⇑f) m := by
  have h := tsum_eq_tsum_piFourier h_norm h_sum 0
  simp only [zero_add] at h
  rw [h]
  have h0 : toTorus (0 : d → ℝ) = 0 := by
    funext i; show ((0:ℝ) : AddCircle (1:ℝ)) = 0; exact QuotientAddGroup.mk_zero _
  refine tsum_congr fun m => ?_
  have h1 : UnitAddTorus.mFourier (d := d) m 0 = 1 := by
    rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
    refine Finset.prod_eq_one fun i _ => ?_
    exact fourier_eval_zero (m i)
  rw [h0, h1, mul_one]

end Coefficient

end Deep.Analytic

end

end TcFold_M4aTheta_PiPoisson

section TcFold_M4aTheta_LatticePoisson

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Real MeasureTheory Set Function Topology Module
open TopologicalSpace (Compacts)
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private theorem innerBilin_nondegenerate : LinearMap.BilinForm.Nondegenerate (innerₗ E) := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro y hy
    exact inner_self_eq_zero.mp (hy y)

private theorem innerBilin_isSymm : LinearMap.BilinForm.IsSymm (innerₗ E) :=
  LinearMap.BilinForm.isSymm_iff.mpr isSymm_inner

variable (b : Basis ι ℤ L)

private def latticeBasisE : Basis ι ℝ E := Basis.ofZLatticeBasis ℝ L b

private def latticeCoord : E ≃ₗ[ℝ] (ι → ℝ) := (latticeBasisE L b).equivFun

private theorem latticeCoord_coe_lattice (v : L) :
    latticeCoord L b (v : E) = Deep.Analytic.intVec (b.equivFun v) := by
  funext i
  simp [latticeCoord, latticeBasisE, Deep.Analytic.intVec, Basis.equivFun_apply,
    Basis.ofZLatticeBasis_repr_apply]

private theorem latticeCoord_symm_intVec (n : ι → ℤ) :
    (latticeCoord L b).symm (Deep.Analytic.intVec n) = (b.equivFun.symm n : E) := by
  have h := latticeCoord_coe_lattice L b (b.equivFun.symm n)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h, LinearEquiv.symm_apply_apply]

private def latticeCoordHomeo : E ≃ₜ (ι → ℝ) :=
  (latticeCoord L b).toContinuousLinearEquiv.toHomeomorph

private theorem latticeCoordHomeo_coe : ⇑(latticeCoordHomeo L b) = ⇑(latticeCoord L b) := rfl

private theorem norm_restrict_comp_latticeCoord (g : C(E, ℂ)) (K : Compacts (ι → ℝ)) :
    ‖(g.comp ((latticeCoordHomeo L b).symm : C((ι → ℝ), E))).restrict (K : Set (ι → ℝ))‖
      = ‖g.restrict ((K.map (latticeCoordHomeo L b).symm
          (latticeCoordHomeo L b).symm.continuous : Compacts E) : Set E)‖ := by
  refine le_antisymm ?_ ?_
  · rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    rintro ⟨x, hx⟩
    exact ContinuousMap.norm_coe_le_norm
      (g.restrict ((K.map (latticeCoordHomeo L b).symm
        (latticeCoordHomeo L b).symm.continuous : Compacts E) : Set E))
      ⟨(latticeCoordHomeo L b).symm x, by
        simp only [TopologicalSpace.Compacts.coe_map]
        exact ⟨x, hx, rfl⟩⟩
  · rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    rintro ⟨y, hy⟩
    simp only [TopologicalSpace.Compacts.coe_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ContinuousMap.norm_coe_le_norm
      ((g.comp ((latticeCoordHomeo L b).symm : C((ι → ℝ), E))).restrict (K : Set (ι → ℝ)))
      ⟨x, hx⟩

section Transport

variable {f : C(E, ℂ)}

private def coordPullback (f : C(E, ℂ)) : C((ι → ℝ), ℂ) :=
  f.comp ((latticeCoordHomeo L b).symm : C((ι → ℝ), E))

private theorem coordPullback_apply (y : ι → ℝ) : coordPullback L b f y = f ((latticeCoord L b).symm y) := rfl

private theorem translate_coordPullback (n : ι → ℤ) :
    Deep.Analytic.translate (coordPullback L b f) n
      = coordPullback L b (f.comp (ContinuousMap.addRight ((b.equivFun.symm n : L) : E))) := by
  ext y
  show f ((latticeCoord L b).symm (y + Deep.Analytic.intVec n))
    = f ((latticeCoord L b).symm y + ((b.equivFun.symm n : L) : E))
  rw [map_add, latticeCoord_symm_intVec]

private theorem translateNorm_summable_transport
    (h_norm : ∀ K : Compacts E,
      Summable fun v : L => ‖(f.comp (ContinuousMap.addRight (v : E))).restrict
        (K : Set E)‖) :
    ∀ K : Compacts (ι → ℝ),
      Summable fun n : ι → ℤ =>
        ‖(Deep.Analytic.translate (coordPullback L b f) n).restrict (K : Set (ι → ℝ))‖ := by
  intro K
  have hre : ∀ n : ι → ℤ,
      ‖(f.comp (ContinuousMap.addRight (((b.equivFun.symm n : L) : E)))).restrict
          ((K.map (latticeCoordHomeo L b).symm
            (latticeCoordHomeo L b).symm.continuous : Compacts E) : Set E)‖
        = ‖(Deep.Analytic.translate (coordPullback L b f) n).restrict (K : Set (ι → ℝ))‖ := by
    intro n
    rw [translate_coordPullback, coordPullback, ContinuousMap.comp_assoc, ← norm_restrict_comp_latticeCoord]
    rfl
  exact ((h_norm (K.map (latticeCoordHomeo L b).symm
    (latticeCoordHomeo L b).symm.continuous)).comp_injective
      (b.equivFun.symm.toEquiv.injective)).congr hre

end Transport

private def dualBasisE : Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis (innerₗ E) (innerBilin_nondegenerate (E := E)) (latticeBasisE L b)

private theorem inner_dualBasisE (x : E) (j : ι) :
    ⟪x, dualBasisE L b j⟫ = latticeCoord L b x j := by
  conv_lhs => rw [← (latticeBasisE L b).sum_repr x]
  rw [sum_inner]
  have hij : ∀ i, ⟪(latticeBasisE L b) i, dualBasisE L b j⟫ = if i = j then 1 else 0 := by
    intro i
    have h := LinearMap.BilinForm.apply_dualBasis_right (B := innerₗ E)
      (innerBilin_nondegenerate (E := E)) (innerBilin_isSymm (E := E)) (latticeBasisE L b) i j
    simpa [dualBasisE] using h
  have hterm : ∀ i, ⟪(latticeBasisE L b).repr x i • (latticeBasisE L b) i, dualBasisE L b j⟫
      = (latticeBasisE L b).repr x i * (if i = j then 1 else 0) := by
    intro i
    rw [real_inner_smul_left, hij]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp [latticeCoord, Basis.equivFun_apply]

private def dualVec (m : ι → ℤ) : E := ∑ i, m i • dualBasisE L b i

private theorem inner_dualVec (x : E) (m : ι → ℤ) :
    ⟪x, dualVec L b m⟫ = ∑ i, (m i : ℝ) * latticeCoord L b x i := by
  rw [dualVec, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, inner_dualBasisE]

private theorem dualSubmodule_eq_span_dualBasisE :
    LinearMap.BilinForm.dualSubmodule (innerₗ E) L
      = Submodule.span ℤ (Set.range (dualBasisE L b)) := by
  have hspan : Submodule.span ℤ (Set.range ⇑(latticeBasisE L b)) = L :=
    b.ofZLatticeBasis_span ℝ
  have h : LinearMap.BilinForm.dualSubmodule (innerₗ E)
        (Submodule.span ℤ (Set.range ⇑(latticeBasisE L b)))
      = Submodule.span ℤ (Set.range ⇑(LinearMap.BilinForm.dualBasis (innerₗ E)
          (innerBilin_nondegenerate (E := E)) (latticeBasisE L b))) :=
    LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ E)
      (innerBilin_nondegenerate (E := E)) (latticeBasisE L b)
  rw [hspan] at h
  exact h

private def dualBasisZ : Basis ι ℤ (Submodule.span ℤ (Set.range ⇑(dualBasisE L b))) :=
  (dualBasisE L b).restrictScalars ℤ

private def dualEnum : (ι → ℤ) ≃ Submodule.span ℤ (Set.range ⇑(dualBasisE L b)) :=
  (dualBasisZ L b).equivFun.symm.toEquiv

private theorem dualEnum_coe (m : ι → ℤ) : ((dualEnum L b m : _) : E) = dualVec L b m := by
  show (((dualBasisZ L b).equivFun.symm m : _) : E) = _
  rw [Basis.equivFun_symm_apply, dualVec]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by
    simp [dualBasisZ, Basis.restrictScalars_apply]

private theorem map_latticeCoord_volume :
    Measure.map (⇑(latticeCoord L b)) volume
      = ENNReal.ofReal (ZLattice.covolume L volume) • volume := by
  have hme : Measurable ⇑(latticeCoord L b) := by
    rw [← latticeCoordHomeo_coe]
    exact (latticeCoordHomeo L b).continuous.measurable
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply hme ht, Measure.smul_apply, smul_eq_mul]
  have h194 := ZLattice.volume_image_eq_volume_div_covolume' L b
    (s := ⇑(latticeCoord L b) ⁻¹' t) ((hme ht).nullMeasurableSet)
  rw [show ⇑(Basis.ofZLatticeBasis ℝ L b).equivFun = ⇑(latticeCoord L b) from rfl,
    Set.image_preimage_eq _ (latticeCoord L b).surjective] at h194
  have hc0 : ENNReal.ofReal (ZLattice.covolume L volume) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos L volume)).ne'
  rw [h194, mul_comm]
  exact (ENNReal.div_mul_cancel hc0 ENNReal.ofReal_ne_top).symm

private theorem integral_pi_eq_covolume_inv_smul (h : (ι → ℝ) → ℂ) :
    ∫ y, h y = (ZLattice.covolume L volume)⁻¹ • ∫ x, h (latticeCoord L b x) := by
  have hcpos := ZLattice.covolume_pos L volume
  have hmeq : ⇑((latticeCoordHomeo L b).toMeasurableEquiv) = ⇑(latticeCoord L b) := rfl
  have hmap : ∫ y, h y ∂(Measure.map (⇑(latticeCoord L b)) volume)
      = ∫ x, h (latticeCoord L b x) := by
    rw [← hmeq]
    exact MeasureTheory.integral_map_equiv ((latticeCoordHomeo L b).toMeasurableEquiv) h
  refine (eq_comm.trans (inv_smul_eq_iff₀ hcpos.ne')).mpr ?_
  rw [← hmap, map_latticeCoord_volume, integral_smul_measure,
    ENNReal.toReal_ofReal hcpos.le]

private theorem mFourier_toTorus_eq_exp (m : ι → ℤ) (y : ι → ℝ) :
    UnitAddTorus.mFourier (-m) (Deep.Analytic.toTorus y)
      = Complex.exp (-(2 * (π : ℂ) * Complex.I) * ∑ i, (m i : ℂ) * (y i : ℂ)) := by
  rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  have hterm : ∀ i : ι, fourier ((-m) i) ((Deep.Analytic.toTorus y) i)
      = Complex.exp (-(2 * (π : ℂ) * Complex.I) * ((m i : ℂ) * (y i : ℂ))) := by
    intro i
    show fourier (-m i) ((y i : ℝ) : AddCircle (1 : ℝ)) = _
    rw [fourier_coe_apply]
    push_cast
    ring_nf
  calc (∏ i, fourier ((-m) i) ((Deep.Analytic.toTorus y) i))
      = ∏ i, Complex.exp (-(2 * (π : ℂ) * Complex.I) * ((m i : ℂ) * (y i : ℂ))) :=
        Finset.prod_congr rfl fun i _ => hterm i
    _ = Complex.exp (∑ i, -(2 * (π : ℂ) * Complex.I) * ((m i : ℂ) * (y i : ℂ))) := by
        rw [Complex.exp_sum]
    _ = Complex.exp (-(2 * (π : ℂ) * Complex.I) * ∑ i, (m i : ℂ) * (y i : ℂ)) := by
        rw [← Finset.mul_sum]

private theorem piFourier_coordPullback_eq (f : C(E, ℂ)) (m : ι → ℤ) :
    Deep.Analytic.piFourier (⇑(coordPullback L b f)) m
      = ((ZLattice.covolume L volume : ℂ))⁻¹ * 𝓕 (⇑f) (dualVec L b m) := by
  rw [Deep.Analytic.piFourier, integral_pi_eq_covolume_inv_smul L b]
  rw [Complex.real_smul, Complex.ofReal_inv]
  congr 1
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [coordPullback_apply, LinearEquiv.symm_apply_apply, mFourier_toTorus_eq_exp,
    smul_eq_mul, inner_dualVec]
  congr 2
  push_cast
  ring

private theorem tsum_lattice_eq_covolume_inv_mul_tsum_fourier (f : C(E, ℂ))
    (h_norm : ∀ K : Compacts E,
      Summable fun v : L => ‖(f.comp (ContinuousMap.addRight (v : E))).restrict
        (K : Set E)‖)
    (h_sum : Summable fun w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L =>
      𝓕 (⇑f) (w : E)) :
    ∑' v : L, f (v : E)
      = ((ZLattice.covolume L volume : ℂ))⁻¹
          * ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L, 𝓕 (⇑f) (w : E) := by
  classical
  let b : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  have hmemIff : ∀ x : E, x ∈ Submodule.span ℤ (Set.range ⇑(dualBasisE L b))
      ↔ x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L := fun x => by
    rw [dualSubmodule_eq_span_dualBasisE L b]
  let eSet : Submodule.span ℤ (Set.range ⇑(dualBasisE L b))
      ≃ LinearMap.BilinForm.dualSubmodule (innerₗ E) L :=
    { toFun := fun w => ⟨w.1, (hmemIff w.1).mp w.2⟩
      invFun := fun w => ⟨w.1, (hmemIff w.1).mpr w.2⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl }
  have heSetCoe : ∀ w, ((eSet w : _) : E) = (w : E) := fun w => rfl

  have hsumS : Summable fun w : Submodule.span ℤ (Set.range ⇑(dualBasisE L b)) =>
      𝓕 (⇑f) (w : E) :=
    (h_sum.comp_injective eSet.injective).congr fun w => by rw [comp_apply, heSetCoe]
  have hsumW : Summable fun m : Module.Free.ChooseBasisIndex ℤ L → ℤ => 𝓕 (⇑f) (dualVec L b m) :=
    (hsumS.comp_injective (dualEnum L b).injective).congr fun m => by
      rw [comp_apply, dualEnum_coe]
  have hs' : Summable fun m : Module.Free.ChooseBasisIndex ℤ L → ℤ =>
      Deep.Analytic.piFourier (⇑(coordPullback L b f)) m :=
    (hsumW.mul_left (((ZLattice.covolume L volume : ℂ))⁻¹)).congr fun m =>
      (piFourier_coordPullback_eq L b f m).symm
  have hn' := translateNorm_summable_transport L b h_norm

  have hseg1 := Deep.Analytic.tsum_intVec_eq_tsum_piFourier hn' hs'
  have hlhs : ∑' v : L, f (v : E)
      = ∑' n : Module.Free.ChooseBasisIndex ℤ L → ℤ, (coordPullback L b f) (Deep.Analytic.intVec n) := by
    rw [← b.equivFun.symm.toEquiv.tsum_eq (fun v : L => f (v : E))]
    exact tsum_congr fun n => by
      rw [coordPullback_apply, latticeCoord_symm_intVec]
      rfl
  have hrhs : ∑' m : Module.Free.ChooseBasisIndex ℤ L → ℤ, Deep.Analytic.piFourier (⇑(coordPullback L b f)) m
      = ((ZLattice.covolume L volume : ℂ))⁻¹
          * ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L, 𝓕 (⇑f) (w : E) := by
    calc ∑' m : Module.Free.ChooseBasisIndex ℤ L → ℤ, Deep.Analytic.piFourier (⇑(coordPullback L b f)) m
        = ∑' m : Module.Free.ChooseBasisIndex ℤ L → ℤ, ((ZLattice.covolume L volume : ℂ))⁻¹
            * 𝓕 (⇑f) (dualVec L b m) :=
          tsum_congr fun m => piFourier_coordPullback_eq L b f m
      _ = ((ZLattice.covolume L volume : ℂ))⁻¹
            * ∑' m : Module.Free.ChooseBasisIndex ℤ L → ℤ, 𝓕 (⇑f) (dualVec L b m) := tsum_mul_left
      _ = ((ZLattice.covolume L volume : ℂ))⁻¹
            * ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L, 𝓕 (⇑f) (w : E) := by
          congr 1
          rw [← eSet.tsum_eq (fun w : (LinearMap.BilinForm.dualSubmodule (innerₗ E) L :
            Set E) => 𝓕 (⇑f) (w : E))]
          rw [← (dualEnum L b).tsum_eq (fun w : Submodule.span ℤ
            (Set.range ⇑(dualBasisE L b)) => 𝓕 (⇑f) ((eSet w : _) : E))]
          exact tsum_congr fun m => by rw [heSetCoe, dualEnum_coe]
  rw [hlhs, hseg1, hrhs]

end Deep.Analytic

end

end TcFold_M4aTheta_LatticePoisson

section TcFold_M4aTheta_Theta

open Real NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {E : Type*} [NormedAddCommGroup E]

private def LatticeThetaSummable (L : Submodule ℤ E) (t : ℝ) : Prop :=
  Summable fun v : L => Real.exp (-π * t * ‖(v : E)‖ ^ 2)

variable (K : Type) [Field K] [NumberField K]

end Deep.Analytic

end

end TcFold_M4aTheta_Theta

section TcFold_M4aTheta_ThetaSummable

open Real NumberField Filter Module

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem latticeThetaSummable (L : Submodule ℤ E) [DiscreteTopology L]
    {t : ℝ} (ht : 0 < t) : LatticeThetaSummable L t := by
  have hπt : 0 < π * t := mul_pos Real.pi_pos ht
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank ℤ L = d := ⟨_, rfl⟩
  set r : ℝ := -(2 * ((d : ℝ) + 1)) with hrdef
  have hr : r < -(Module.finrank ℤ L : ℝ) := by
    rw [hrdef, hd]
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hg : Summable fun z : L => ‖z‖ ^ r := ZLattice.summable_norm_rpow L r hr
  set C : ℝ := ((d + 1).factorial : ℝ) / (π * t) ^ (d + 1) with hCdef
  show Summable fun v : L => Real.exp (-π * t * ‖(v : E)‖ ^ 2)
  refine Summable.of_norm_bounded_eventually (hg.mul_left C) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton 0) ?_
  intro v hv
  simp only [Set.mem_setOf_eq, not_le] at hv
  rcases eq_or_ne v 0 with h0 | h0
  · exact h0
  exfalso

  have hvn : (0 : ℝ) < ‖(v : E)‖ := by
    rw [norm_pos_iff]
    exact fun h => h0 (by exact_mod_cast Subtype.ext h)
  set a : ℝ := π * t * ‖(v : E)‖ ^ 2 with hadef
  have ha0 : 0 < a := mul_pos hπt (pow_pos hvn 2)
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (d + 1)

  have h1 : a ^ (d + 1) ≤ Real.exp a * ((d + 1).factorial : ℝ) :=
    (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp a ha0.le (d + 1))
  have h2 : Real.exp (-a) ≤ ((d + 1).factorial : ℝ) / a ^ (d + 1) := by
    rw [le_div_iff₀ (pow_pos ha0 _), Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos a)]
    exact h1

  have hrpow : ‖(v : E)‖ ^ r = (‖(v : E)‖ ^ (2 * (d + 1) : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast ‖(v : E)‖ (2 * (d + 1)), ← Real.rpow_neg (norm_nonneg _),
      hrdef]
    norm_num
  have hapow : a ^ (d + 1) = (π * t) ^ (d + 1) * ‖(v : E)‖ ^ (2 * (d + 1) : ℕ) := by
    rw [hadef, mul_pow, ← pow_mul]
  have hbound : Real.exp (-π * t * ‖(v : E)‖ ^ 2) ≤ C * ‖(v : E)‖ ^ r := by
    have : -π * t * ‖(v : E)‖ ^ 2 = -a := by rw [hadef]; ring
    rw [this, hrpow, hCdef]
    refine h2.trans_eq ?_
    rw [hapow]
    field_simp
  have hnorm : ‖Real.exp (-π * t * ‖(v : E)‖ ^ 2)‖ = Real.exp (-π * t * ‖(v : E)‖ ^ 2) :=
    Real.norm_of_nonneg (Real.exp_pos _).le

  have hcoe : ‖v‖ = ‖(v : E)‖ := rfl
  rw [hnorm, hcoe] at hv
  exact (hv.trans_le hbound).false

end Deep.Analytic

end TcFold_M4aTheta_ThetaSummable

section TcFold_M4aTheta_GaussPoisson

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

p2m_open "Real MeasureTheory Set Function Topology Module Complex Function.Complex Matrix"
open TopologicalSpace (Compacts)
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private def gaussianMap (t : ℝ) : C(E, ℂ) :=
  ⟨fun x => (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ),
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.mul
        ((continuous_norm).pow 2))))⟩

private theorem gaussianMap_apply (t : ℝ) (x : E) :
    gaussianMap t x = (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) := rfl

private theorem norm_gaussianMap (t : ℝ) (x : E) :
    ‖gaussianMap t x‖ = Real.exp (-π * t * ‖x‖ ^ 2) := by
  rw [gaussianMap_apply, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]

private theorem gaussianMap_eq_cexp (t : ℝ) (x : E) :
    gaussianMap t x = Complex.exp (-(((π * t : ℝ)) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  rw [gaussianMap_apply, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem gaussian_translateNorm_summable {t : ℝ} (ht : 0 < t)
    (K : Compacts E) :
    Summable fun v : L =>
      ‖((gaussianMap t).comp (ContinuousMap.addRight (v : E))).restrict
        (K : Set E)‖ := by
  obtain ⟨R, hR0, hRK⟩ := (K.isCompact.isBounded).subset_closedBall_lt 0 0
  have ht4 : (0 : ℝ) < t / 4 := by linarith
  have hsum := Deep.Analytic.latticeThetaSummable L ht4
  rw [Deep.Analytic.LatticeThetaSummable] at hsum
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    (hsum.mul_left (Real.exp (π * t * R ^ 2)))
  rw [← Real.exp_add]
  have hπ := Real.pi_pos
  rcases le_or_gt ‖(v : E)‖ (2 * R) with hv | hv
  ·
    refine le_trans ?_ (Real.one_le_exp ?_)
    · rw [ContinuousMap.norm_le _ zero_le_one]
      rintro ⟨x, hx⟩
      show ‖gaussianMap t (x + (v : E))‖ ≤ 1
      rw [norm_gaussianMap]
      rw [Real.exp_le_one_iff]
      have hpos : 0 ≤ π * t * ‖x + (v : E)‖ ^ 2 := by positivity
      linarith
    · have hv2 : ‖(v : E)‖ ^ 2 ≤ (2 * R) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hv 2
      have hmul : π * t / 4 * ‖(v : E)‖ ^ 2 ≤ π * t / 4 * (2 * R) ^ 2 :=
        mul_le_mul_of_nonneg_left hv2 (by positivity)
      nlinarith [hmul]
  ·
    rw [ContinuousMap.norm_le _ (le_of_lt (Real.exp_pos _))]
    rintro ⟨x, hx⟩
    show ‖gaussianMap t (x + (v : E))‖ ≤ _
    rw [norm_gaussianMap, Real.exp_le_exp]
    have hxR : ‖x‖ ≤ R := by
      have := hRK hx
      simpa using this
    have hlow : ‖(v : E)‖ - R ≤ ‖x + (v : E)‖ := by
      have h1 := norm_add_le (x + (v : E)) (-x)
      simp only [add_neg_cancel_comm, norm_neg] at h1
      linarith
    have hhalf : ‖(v : E)‖ / 2 ≤ ‖x + (v : E)‖ := by linarith
    have hsq : (‖(v : E)‖ / 2) ^ 2 ≤ ‖x + (v : E)‖ ^ 2 :=
      pow_le_pow_left₀ (by linarith) hhalf 2
    have h1 : π * t * ((‖(v : E)‖ / 2) ^ 2) ≤ π * t * ‖x + (v : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 0 ≤ π * t * R ^ 2 := by positivity
    nlinarith [h1, h2]

private scoped instance discreteTopology_dualSubmodule :
    DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) := by
  classical
  rw [Deep.Analytic.dualSubmodule_eq_span_dualBasisE L (Module.Free.chooseBasis ℤ L)]
  infer_instance

private scoped instance isZLattice_dualSubmodule :
    IsZLattice ℝ (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) := by
  classical
  constructor
  rw [Deep.Analytic.dualSubmodule_eq_span_dualBasisE L (Module.Free.chooseBasis ℤ L)]
  exact IsZLattice.span_top

private theorem fourier_gaussianMap {t : ℝ} (ht : 0 < t) (w : E) :
    𝓕 ⇑(gaussianMap (E := E) t) w
      = (1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)
          * Complex.exp (-(π : ℂ) / t * (‖w‖ : ℂ) ^ 2) := by
  have hb : (0 : ℝ) < (((π * t : ℝ) : ℂ)).re := by
    simpa using mul_pos Real.pi_pos ht
  have h𝓕 : ⇑(gaussianMap (E := E) t)
      = fun v : E => Complex.exp (-(((π * t : ℝ)) : ℂ) * ‖v‖ ^ 2) := by
    funext v
    rw [gaussianMap_eq_cexp]
  rw [h𝓕, fourier_gaussian_innerProductSpace hb w]
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt ht
  have hπC : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hbase : (π : ℂ) / ((π * t : ℝ) : ℂ) = 1 / (t : ℂ) := by
    push_cast
    field_simp
  have harg : -(π : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / ((π * t : ℝ) : ℂ)
      = -(π : ℂ) / t * (‖w‖ : ℂ) ^ 2 := by
    push_cast
    field_simp
  rw [hbase, harg]

section Duality

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)

end Duality

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_GaussPoisson
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ResidueCal

p2m_open "Real NumberField NumberField.Units NumberField.InfinitePlace Module Ideal NumberField.Ideal"
open Filter Topology
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

private def heckeDensity : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

private theorem classCoeff_zero (C : ClassGroup (𝓞 K)) :
    Deep.Analytic.classCoeff K C 0 = 0 := by
  have : IsEmpty {I : (Ideal (𝓞 K))⁰ //
      ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) = 0} :=
    ⟨fun I => absNorm_ne_zero_of_nonZeroDivisors I.1 I.2.2⟩
  exact Nat.card_of_isEmpty

private theorem card_norm_le_eq_sum_classCoeff (C : ClassGroup (𝓞 K)) {s : ℝ}
    (hs : 0 < s) :
    (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) =
      ∑ n ∈ Finset.Icc 0 ⌊s⌋₊, (Deep.Analytic.classCoeff K C n : ℝ) := by
  classical
  have hset : {I : (Ideal (𝓞 K))⁰ |
      absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C}.Finite :=
    (finite_setOf_absNorm_le₀ ⌊s⌋₊).subset fun I hI => Nat.le_floor hI.1
  haveI : Fintype {I : (Ideal (𝓞 K))⁰ //
      absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} := hset.fintype
  have key : Nat.card {I : (Ideal (𝓞 K))⁰ //
      absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} =
      ∑ n ∈ Finset.Icc 0 ⌊s⌋₊, Deep.Analytic.classCoeff K C n := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise
        (f := fun I : {I : (Ideal (𝓞 K))⁰ //
            absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} =>
          absNorm (I.1 : Ideal (𝓞 K)))
        (t := Finset.Icc 0 ⌊s⌋₊)
        (fun I _ => Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor I.2.1⟩)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hns : (n : ℝ) ≤ s := (Nat.le_floor_iff hs.le).mp (Finset.mem_Icc.mp hn).2
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, by rw [y.2.2]; exact hns, y.2.1⟩, y.2.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  rw [key]
  push_cast
  rfl

private theorem tendsto_sum_classCoeff_div (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊s⌋₊,
        (Deep.Analytic.classCoeff K C n : ℝ)) / s) atTop
      (𝓝 (heckeDensity K)) := by
  refine Tendsto.congr' ?_
    (NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K C)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [card_norm_le_eq_sum_classCoeff K C hs]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ResidueCal
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ClassSummable

set_option maxHeartbeats 1600000

p2m_open "Real NumberField NumberField.Units NumberField.InfinitePlace Module Ideal NumberField.Ideal"
open Filter Topology MeasureTheory Set
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

private scoped instance finite_classNormFiber (C : ClassGroup (𝓞 K)) (n : ℕ) :
    Finite {I : (Ideal (𝓞 K))⁰ //
      ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) = n} :=
  Set.Finite.to_subtype <|
    (finite_setOf_absNorm_le₀ n).subset fun _ hI => le_of_eq hI.2

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ClassSummable
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ConeTheta

p2m_open "Real NumberField NumberField.Units NumberField.mixedEmbedding Ideal NumberField.Ideal Submodule"
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ConeTheta
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ConeSummable

open Real NumberField NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ConeSummable
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ConeLayers

p2m_open "Real NumberField NumberField.Units NumberField.mixedEmbedding Ideal NumberField.Ideal Submodule"
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

open Classical in

private scoped instance countable_idealSet (J : (Ideal (𝓞 K))⁰) :
    Countable (idealSet K J) := by
  have h1 : Countable
      (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) := inferInstance
  have h2 : (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) :
      Set (mixedSpace K)).Countable := by
    rw [← Set.countable_coe_iff]
    exact h1
  have h3 : (idealSet K J).Countable := h2.mono fun a ha => ha.2
  exact h3.to_subtype

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ConeLayers
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ConeGauss

p2m_open "Real NumberField NumberField.Units NumberField.mixedEmbedding Ideal NumberField.Ideal Submodule"
open NumberField.mixedEmbedding.fundamentalCone
open MeasureTheory Set
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ConeGauss
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_AbelTheta

set_option maxHeartbeats 1600000

p2m_open "Real NumberField Module Ideal NumberField.Ideal"
open Filter Topology MeasureTheory Set
open scoped nonZeroDivisors

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable (K : Type) [Field K] [NumberField K]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_AbelTheta
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ThetaFE

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

p2m_open "Real MeasureTheory Set Function Topology Module Complex Function.Complex"
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E)

private theorem exists_min_norm [DiscreteTopology L] :
    ∃ m : ℝ, 0 < m ∧ ∀ v : L, v ≠ 0 → m ≤ ‖(v : E)‖ := by
  have h0 : IsOpen ({0} : Set L) := isOpen_discrete _
  rw [Metric.isOpen_iff] at h0
  obtain ⟨ε, hε, hball⟩ := h0 0 rfl
  refine ⟨ε, hε, fun v hv => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  refine hv ?_
  have hmem : v ∈ Metric.ball (0 : L) ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, ZeroMemClass.coe_zero,
      dist_zero_right]
    exact hlt
  simpa using hball hmem

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ThetaFE
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_LatticeFE

set_option maxHeartbeats 3200000

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

open Real MeasureTheory Set Function Topology Module Filter Asymptotics
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E)

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_LatticeFE
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_IdealFE

set_option maxHeartbeats 3200000

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

open Real MeasureTheory Set Function Topology Module Filter NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped nonZeroDivisors RealInnerProductSpace Classical

variable (K : Type) [Field K] [NumberField K]

private scoped instance discreteTopology_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (Deep.Analytic.euclideanIdealLattice K I) := by
  classical
  rw [Deep.Analytic.euclideanIdealLattice]
  infer_instance

private scoped instance isZLattice_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (Deep.Analytic.euclideanIdealLattice K I) := by
  classical
  simp_rw [Deep.Analytic.euclideanIdealLattice]
  infer_instance

private def dualIdealUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

open Classical in

private theorem covolume_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (Deep.Analytic.euclideanIdealLattice K I) volume
      = (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K))
          * (2⁻¹) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| := by
  have h1 : ZLattice.covolume (Deep.Analytic.euclideanIdealLattice K I) volume
      = ZLattice.covolume (mixedEmbedding.idealLattice K I) volume :=
    ZLattice.covolume_comap (mixedEmbedding.idealLattice K I) volume volume
      (euclidean.volumePreserving_toMixed K)
  exact h1.trans (mixedEmbedding.covolume_idealLattice (K := K) I)

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_IdealFE
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ConjDilPoisson

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

open Real MeasureTheory Set Function Topology Module Matrix NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped nonZeroDivisors RealInnerProductSpace Classical

variable (K : Type) [Field K] [NumberField K]

private def mixedConjDilCLE :
    euclidean.mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mixedConjDil K).toContinuousLinearEquiv

variable (L : Submodule ℤ (euclidean.mixedSpace K))
  [DiscreteTopology L] [IsZLattice ℝ L]

private abbrev mixedConjDilLattice : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ L (mixedConjDilCLE K).symm.toLinearMap

private theorem mem_mixedConjDilLattice (z : euclidean.mixedSpace K) :
    z ∈ mixedConjDilLattice K L ↔ (mixedConjDil K).symm z ∈ L :=
  Iff.rfl

private def mixedConjDilDiag : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun p => if p.2 = (0 : Fin 2) then 2 else -2)

private theorem euclideanRepr_mixedConjDil (x : euclidean.mixedSpace K) (i : index K) :
    (euclidean.stdOrthonormalBasis K).repr (mixedConjDil K x) i
      = mixedConjDilDiag K i * (euclidean.stdOrthonormalBasis K).repr x i := by
  rcases i with v | ⟨w, k⟩
  · simp [mixedConjDilDiag, euclideanRepr_inl, mixedConjDil_apply_fst]
  · fin_cases k
    · simp [mixedConjDilDiag, euclideanRepr_inr_re, mixedConjDil_apply_snd]
    · simp [mixedConjDilDiag, euclideanRepr_inr_im, mixedConjDil_apply_snd]

private theorem inner_mixedConjDil (x y : euclidean.mixedSpace K) :
    inner ℝ (mixedConjDil K x) y = inner ℝ x (mixedConjDil K y) := by
  rw [← (euclidean.stdOrthonormalBasis K).sum_inner_mul_inner
      (mixedConjDil K x) y,
    ← (euclidean.stdOrthonormalBasis K).sum_inner_mul_inner x
      (mixedConjDil K y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : ∀ z : euclidean.mixedSpace K,
      (inner ℝ z ((euclidean.stdOrthonormalBasis K) i) : ℝ)
        = (euclidean.stdOrthonormalBasis K).repr z i := fun z => by
    rw [real_inner_comm, OrthonormalBasis.repr_apply_apply]
  have hl : ∀ z : euclidean.mixedSpace K,
      (inner ℝ ((euclidean.stdOrthonormalBasis K) i) z : ℝ)
        = (euclidean.stdOrthonormalBasis K).repr z i := fun z => by
    rw [OrthonormalBasis.repr_apply_apply]
  rw [hr, hr, hl, hl, euclideanRepr_mixedConjDil, euclideanRepr_mixedConjDil]
  ring

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ConjDilPoisson
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ConjDilFE

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

open Real MeasureTheory Set Function Topology Filter Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]
variable (L : Submodule ℤ (euclidean.mixedSpace K))
  [DiscreteTopology L] [IsZLattice ℝ L]

private abbrev mixedConjDilSymmLattice : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ
    (LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) L)
    (mixedConjDilCLE K).toLinearMap

private scoped instance isZLattice_mixedConjDilSymmLattice : IsZLattice ℝ (mixedConjDilSymmLattice K L) :=
  instIsZLatticeComap ℝ
    (LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) L)
    (mixedConjDilCLE K)

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ConjDilFE
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_IdealDual

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

p2m_open "Real MeasureTheory Set Function Topology Filter Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic Finset Set.Finset"

open scoped nonZeroDivisors Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

private def euclideanEmbedding : K →ₗ[ℤ] euclidean.mixedSpace K :=
  (((euclidean.toMixed K).symm.toLinearMap).restrictScalars ℤ).comp
    (mixedEmbedding K).toIntAlgHom.toLinearMap

private theorem euclideanEmbedding_apply (x : K) :
    euclideanEmbedding K x = (euclidean.toMixed K).symm (mixedEmbedding K x) := rfl

private def mixedConjDilLinearMap : euclidean.mixedSpace K →ₗ[ℤ] euclidean.mixedSpace K :=
  (mixedConjDil K).toLinearMap.restrictScalars ℤ

private theorem mixedConjDilLinearMap_apply (v : euclidean.mixedSpace K) :
    mixedConjDilLinearMap K v = mixedConjDil K v := rfl

private theorem mem_euclideanIdealLattice (N : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : euclidean.mixedSpace K) :
    v ∈ Deep.Analytic.euclideanIdealLattice K N
      ↔ ∃ y ∈ (N : FractionalIdeal (𝓞 K)⁰ K),
          (euclidean.toMixed K).symm (mixedEmbedding K y) = v := by
  rw [Deep.Analytic.euclideanIdealLattice, ZLattice.comap, Submodule.mem_comap]
  rw [mem_idealLattice]
  change (∃ y ∈ (N : Set K), mixedEmbedding K y = euclidean.toMixed K v) ↔ _
  constructor
  · rintro ⟨y, hy, hyv⟩
    exact ⟨y, hy, by rw [hyv]; exact (euclidean.toMixed K).symm_apply_apply v⟩
  · rintro ⟨y, hy, hyv⟩
    refine ⟨y, hy, ?_⟩
    rw [← hyv]
    exact ((euclidean.toMixed K).apply_symm_apply _).symm

private theorem euclideanIdealLattice_eq_map (N : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Deep.Analytic.euclideanIdealLattice K N
      = Submodule.map (euclideanEmbedding K)
          (((N : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ) := by
  ext v
  rw [mem_euclideanIdealLattice, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyv⟩
    exact ⟨y, by simpa using hy, hyv⟩
  · rintro ⟨y, hy, hyv⟩
    exact ⟨y, by simpa using hy, hyv⟩

private def euclideanIdealLatticeBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℝ (euclidean.mixedSpace K) :=
  (fractionalIdealLatticeBasis K I).map (euclidean.toMixed K).symm.toLinearEquiv

private theorem euclideanIdealLatticeBasis_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    euclideanIdealLatticeBasis K I i = euclideanEmbedding K (basisOfFractionalIdeal K I i) := by
  rw [euclideanIdealLatticeBasis, Basis.map_apply, fractionalIdealLatticeBasis_apply]
  rfl

private theorem euclideanIdealLattice_eq_span (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Deep.Analytic.euclideanIdealLattice K I
      = Submodule.span ℤ (Set.range (euclideanIdealLatticeBasis K I)) := by
  have hr : Set.range (euclideanIdealLatticeBasis K I)
      = ((euclidean.toMixed K).symm.toLinearMap.restrictScalars ℤ) ''
          Set.range (fractionalIdealLatticeBasis K I) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => by
      rw [euclideanIdealLatticeBasis, Basis.map_apply]; rfl)
  rw [hr, ← Submodule.map_span]
  ext v
  rw [Submodule.mem_map, mem_euclideanIdealLattice]
  constructor
  · rintro ⟨y, hy, hyv⟩
    refine ⟨mixedEmbedding K y, ?_, hyv⟩
    rw [mem_span_fractionalIdealLatticeBasis]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    rw [mem_span_fractionalIdealLatticeBasis] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    exact ⟨y, hy, by rw [← hwv, ← hyw]; rfl⟩

private theorem fractionalIdeal_restrictScalars_eq_span (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ)
      = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) := by
  ext x
  rw [mem_span_basisOfFractionalIdeal]
  simp

private theorem span_traceDual_basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual)
      = ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)
          : Submodule (𝓞 K) K).restrictScalars ℤ) := by
  rw [FractionalIdeal.coe_dual ℤ ℚ (Units.ne_zero I)]
  exact (Submodule.traceDual_span_of_basis ℤ
    ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
    (basisOfFractionalIdeal K I) (fractionalIdeal_restrictScalars_eq_span K I)).symm

private theorem inner_ext_basis {ι : Type} [Finite ι] (b : Basis ι ℝ (euclidean.mixedSpace K))
    {v w : euclidean.mixedSpace K}
    (h : ∀ j, inner ℝ v (b j) = (inner ℝ w (b j) : ℝ)) : v = w := by
  have hz : innerₗ (euclidean.mixedSpace K) (v - w) = 0 := by
    apply b.ext
    intro j
    rw [LinearMap.zero_apply, innerₗ_apply_apply, inner_sub_left, h j, sub_self]
  have := (Deep.Analytic.innerBilin_nondegenerate
      (E := euclidean.mixedSpace K)).1 (v - w)
    (fun y => by rw [hz, LinearMap.zero_apply])
  exact sub_eq_zero.mp this

private theorem dualBasis_euclideanIdealLatticeBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    LinearMap.BilinForm.dualBasis (innerₗ (euclidean.mixedSpace K))
        (Deep.Analytic.innerBilin_nondegenerate) (euclideanIdealLatticeBasis K I) i
      = mixedConjDil K (euclideanEmbedding K ((basisOfFractionalIdeal K I).traceDual i)) := by
  apply inner_ext_basis K (euclideanIdealLatticeBasis K I)
  intro j
  have hL : inner ℝ (LinearMap.BilinForm.dualBasis (innerₗ (euclidean.mixedSpace K))
      Deep.Analytic.innerBilin_nondegenerate (euclideanIdealLatticeBasis K I) i) (euclideanIdealLatticeBasis K I j)
      = if j = i then (1 : ℝ) else 0 := by
    rw [← innerₗ_apply_apply]
    exact LinearMap.BilinForm.apply_dualBasis_left
      Deep.Analytic.innerBilin_nondegenerate (euclideanIdealLatticeBasis K I) i j
  have hR : inner ℝ (mixedConjDil K
        (euclideanEmbedding K ((basisOfFractionalIdeal K I).traceDual i)))
      (euclideanIdealLatticeBasis K I j) = if j = i then (1 : ℝ) else 0 := by
    rw [euclideanIdealLatticeBasis_apply, inner_mixedConjDil, euclideanEmbedding_apply, euclideanEmbedding_apply,
      Deep.Analytic.inner_mixedConjDil_eq_trace,
      show Algebra.trace ℚ K ((basisOfFractionalIdeal K I).traceDual i
          * basisOfFractionalIdeal K I j)
        = if j = i then (1 : ℚ) else 0 from
        (basisOfFractionalIdeal K I).trace_traceDual_mul i j]
    rw [apply_ite (fun q : ℚ => ((q : ℚ) : ℝ))]
    norm_num
  rw [hL, hR]

private theorem map_mixedConjDil_eq_mixedConjDilLattice (N : Submodule ℤ (euclidean.mixedSpace K))
    [DiscreteTopology N] [IsZLattice ℝ N] :
    Submodule.map (mixedConjDilLinearMap K) N = mixedConjDilLattice K N := by
  ext z
  rw [Submodule.mem_map, mem_mixedConjDilLattice]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rw [← hwz, mixedConjDilLinearMap_apply, (mixedConjDil K).symm_apply_apply]
    exact hw
  · intro hz
    exact ⟨(mixedConjDil K).symm z, hz, by
      rw [mixedConjDilLinearMap_apply, (mixedConjDil K).apply_symm_apply]⟩

private theorem dual_euclideanIdealLattice (I Idual : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hdual : (Idual : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K))
        (Deep.Analytic.euclideanIdealLattice K I)
      = mixedConjDilLattice K (Deep.Analytic.euclideanIdealLattice K Idual) := by
  rw [euclideanIdealLattice_eq_span K I,
    LinearMap.BilinForm.dualSubmodule_span_of_basis _
      Deep.Analytic.innerBilin_nondegenerate (euclideanIdealLatticeBasis K I)]
  have hrange : Set.range (LinearMap.BilinForm.dualBasis
        (innerₗ (euclidean.mixedSpace K))
        Deep.Analytic.innerBilin_nondegenerate (euclideanIdealLatticeBasis K I))
      = (mixedConjDilLinearMap K) '' ((euclideanEmbedding K) ''
          Set.range (basisOfFractionalIdeal K I).traceDual) := by
    rw [← Set.range_comp, ← Set.range_comp]
    exact congrArg Set.range (funext fun i => dualBasis_euclideanIdealLatticeBasis K I i)
  rw [hrange, ← Submodule.map_span, ← Submodule.map_span, span_traceDual_basisOfFractionalIdeal,
    ← hdual, ← euclideanIdealLattice_eq_map K Idual,
    map_mixedConjDil_eq_mixedConjDilLattice K (Deep.Analytic.euclideanIdealLattice K Idual)]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_IdealDual
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ClassLambda

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

p2m_open "Real MeasureTheory Set Function Topology Filter Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic Finset Set.Finset"

open scoped nonZeroDivisors Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

variable (reps dreps : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ClassLambda
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_ChiTheta

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real MeasureTheory Set Filter Topology Asymptotics NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

private theorem abs_discr_pos : 0 < |(discr K : ℝ)| :=
  abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

private theorem absNorm_units_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  have h0 : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    fun h => I.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm h0)

private theorem absNorm_dualIdealUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal.absNorm (dualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
      = (|(discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ))⁻¹ := by
  have hval : (dualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
    simp [dualIdealUnit]
  have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [coeIdeal_differentIdeal (K := ℚ), inv_inv]
  have hnd : (FractionalIdeal.absNorm
      (((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) : ℝ)
        = |(discr K : ℝ)| := by
    rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K)]
    push_cast
    exact (Nat.cast_natAbs (discr K)).trans (by push_cast; rfl)
  rw [hval, FractionalIdeal.dual_eq_mul_inv ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K), map_mul,
    map_inv₀, hd1, map_inv₀]
  push_cast
  rw [hnd, mul_inv]

private def codifferentClass : ClassGroup (𝓞 K) :=
  idealClass K (dualIdealUnit K 1)

private theorem dualIdealUnit_eq_mul_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualIdealUnit K I = dualIdealUnit K 1 * I⁻¹ := by
  refine Units.ext ?_
  simp only [dualIdealUnit, Units.val_mk0, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val]
  exact FractionalIdeal.dual_eq_mul_inv ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)

private theorem idealClass_dualIdealUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealClass K (dualIdealUnit K I) = codifferentClass K * (idealClass K I)⁻¹ := by
  unfold codifferentClass idealClass
  rw [dualIdealUnit_eq_mul_inv K I, map_mul, map_inv]

variable (reps : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_ChiTheta
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_HeckeDTheta

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real MeasureTheory Set Filter Function Topology Asymptotics Module Matrix NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

open scoped nonZeroDivisors RealInnerProductSpace Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

private def sqrtTwoEquiv : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := ((Real.sqrt 2 : ℝ) : ℂ) * z
  invFun z := z / ((Real.sqrt 2 : ℝ) : ℂ)
  map_add' z w := by ring
  map_smul' r z := by
    simp only [RingHom.id_apply, Complex.real_smul]
    ring
  left_inv z := by
    have h : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    show ((Real.sqrt 2 : ℝ) : ℂ) * z / ((Real.sqrt 2 : ℝ) : ℂ) = z
    field_simp
  right_inv z := by
    have h : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    show ((Real.sqrt 2 : ℝ) : ℂ) * (z / ((Real.sqrt 2 : ℝ) : ℂ)) = z
    field_simp

private theorem normSq_sqrtTwoEquiv (z : ℂ) : Complex.normSq (sqrtTwoEquiv z) = 2 * Complex.normSq z := by
  show Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ) * z) = _
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private def mixedPlacewise (φ : ℂ ≃ₗ[ℝ] ℂ) : (euclidean.mixedSpace K) ≃ₗ[ℝ] (euclidean.mixedSpace K) :=
  (WithLp.linearEquiv 2 ℝ _).trans <|
    (((LinearEquiv.refl ℝ (EuclideanSpace ℝ {w : InfinitePlace K // IsReal w})).prodCongr
      ((WithLp.linearEquiv 2 ℝ ({w : InfinitePlace K // IsComplex w} → ℂ)).trans <|
        (LinearEquiv.piCongrRight fun _ : {w : InfinitePlace K // IsComplex w} => φ).trans
          (WithLp.linearEquiv 2 ℝ ({w : InfinitePlace K // IsComplex w} → ℂ)).symm)).trans
      (WithLp.linearEquiv 2 ℝ _).symm)

private theorem mixedPlacewise_apply_fst (φ : ℂ ≃ₗ[ℝ] ℂ) (x : euclidean.mixedSpace K) :
    (mixedPlacewise K φ x).fst = x.fst := by
  simp [mixedPlacewise, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

private theorem mixedPlacewise_apply_snd (φ : ℂ ≃ₗ[ℝ] ℂ) (x : euclidean.mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (mixedPlacewise K φ x).snd w = φ (x.snd w) := by
  simp [mixedPlacewise, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.piCongrRight_apply]

private def mixedDil : (euclidean.mixedSpace K) ≃ₗ[ℝ] (euclidean.mixedSpace K) :=
  mixedPlacewise K sqrtTwoEquiv

private def mixedDilCLE : euclidean.mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mixedDil K).toContinuousLinearEquiv

private theorem mixedDil_apply_fst (x : euclidean.mixedSpace K) : (mixedDil K x).fst = x.fst :=
  mixedPlacewise_apply_fst K _ x

private theorem mixedDil_apply_snd (x : euclidean.mixedSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (mixedDil K x).snd w = ((Real.sqrt 2 : ℝ) : ℂ) * x.snd w :=
  mixedPlacewise_apply_snd K _ x w

private theorem norm_sq_eq_sum (x : euclidean.mixedSpace K) :
    ‖x‖ ^ 2 = (∑ v : {w : InfinitePlace K // IsReal w}, (x.fst v) ^ 2)
      + ∑ w : {w : InfinitePlace K // IsComplex w}, Complex.normSq (x.snd w) := by
  rw [← sum_sq_euclideanRepr K x, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : (∑ v : {w : InfinitePlace K // IsReal w},
      ((euclidean.stdOrthonormalBasis K).repr x (Sum.inl v)) ^ 2)
        = ∑ v : {w : InfinitePlace K // IsReal w}, (x.fst v) ^ 2 :=
    Finset.sum_congr rfl fun v _ => by rw [euclideanRepr_inl]
  have h2 : (∑ w : {w : InfinitePlace K // IsComplex w}, ∑ k : Fin 2,
      ((euclidean.stdOrthonormalBasis K).repr x (Sum.inr (w, k))) ^ 2)
        = ∑ w : {w : InfinitePlace K // IsComplex w}, Complex.normSq (x.snd w) :=
    Finset.sum_congr rfl fun w _ => by
      rw [Fin.sum_univ_two, euclideanRepr_inr_re, euclideanRepr_inr_im, Complex.normSq_apply]
      ring
  rw [h1, h2]

private theorem norm_sq_mixedDil (x : euclidean.mixedSpace K) :
    ‖mixedDil K x‖ ^ 2 = (∑ v : {w : InfinitePlace K // IsReal w}, (x.fst v) ^ 2)
      + ∑ w : {w : InfinitePlace K // IsComplex w}, 2 * Complex.normSq (x.snd w) := by
  rw [norm_sq_eq_sum]
  have h1 : (∑ v : {w : InfinitePlace K // IsReal w}, ((mixedDil K x).fst v) ^ 2)
      = ∑ v : {w : InfinitePlace K // IsReal w}, (x.fst v) ^ 2 :=
    Finset.sum_congr rfl fun v _ => by rw [mixedDil_apply_fst]
  have h2 : (∑ w : {w : InfinitePlace K // IsComplex w}, Complex.normSq ((mixedDil K x).snd w))
      = ∑ w : {w : InfinitePlace K // IsComplex w}, 2 * Complex.normSq (x.snd w) :=
    Finset.sum_congr rfl fun w _ => by
      rw [show (mixedDil K x).snd w = sqrtTwoEquiv (x.snd w) from mixedPlacewise_apply_snd K _ x w,
        normSq_sqrtTwoEquiv]
  rw [h1, h2]

private def dilDiag : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => Real.sqrt 2)

private theorem euclideanRepr_mixedDil (x : euclidean.mixedSpace K) (i : index K) :
    (euclidean.stdOrthonormalBasis K).repr (mixedDil K x) i
      = dilDiag K i * (euclidean.stdOrthonormalBasis K).repr x i := by
  rcases i with v | ⟨w, k⟩
  · simp [dilDiag, euclideanRepr_inl, mixedDil_apply_fst]
  · fin_cases k
    · simp [dilDiag, euclideanRepr_inr_re, mixedDil_apply_snd]
    · simp [dilDiag, euclideanRepr_inr_im, mixedDil_apply_snd]

private theorem prod_dilDiag : ∏ i : index K, dilDiag K i = 2 ^ nrComplexPlaces K := by
  rw [Fintype.prod_sum_type]
  have h1 : (∏ v : {w : InfinitePlace K // IsReal w}, dilDiag K (Sum.inl v)) = 1 := by
    simp [dilDiag]
  have h2 : (∏ p : {w : InfinitePlace K // IsComplex w} × Fin 2, dilDiag K (Sum.inr p))
      = 2 ^ nrComplexPlaces K := by
    rw [Fintype.prod_prod_type]
    have hw : ∀ w : {w : InfinitePlace K // IsComplex w},
        (∏ k : Fin 2, dilDiag K (Sum.inr (w, k))) = 2 := by
      intro w
      rw [Fin.prod_univ_two]
      simp only [dilDiag, Sum.elim_inr]
      exact Real.mul_self_sqrt (by norm_num)
    rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, nrComplexPlaces]
  rw [h1, h2, one_mul]

private theorem inner_mixedDil (x y : euclidean.mixedSpace K) :
    inner ℝ (mixedDil K x) y = inner ℝ x (mixedDil K y) := by
  rw [← (euclidean.stdOrthonormalBasis K).sum_inner_mul_inner (mixedDil K x) y,
    ← (euclidean.stdOrthonormalBasis K).sum_inner_mul_inner x (mixedDil K y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : ∀ z : euclidean.mixedSpace K,
      (inner ℝ z ((euclidean.stdOrthonormalBasis K) i) : ℝ)
        = (euclidean.stdOrthonormalBasis K).repr z i := fun z => by
    rw [real_inner_comm, OrthonormalBasis.repr_apply_apply]
  have hl : ∀ z : euclidean.mixedSpace K,
      (inner ℝ ((euclidean.stdOrthonormalBasis K) i) z : ℝ)
        = (euclidean.stdOrthonormalBasis K).repr z i := fun z => by
    rw [OrthonormalBasis.repr_apply_apply]
  rw [hr, hr, hl, hl, euclideanRepr_mixedDil, euclideanRepr_mixedDil]
  ring

variable (L : Submodule ℤ (euclidean.mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]

private abbrev mixedDilLattice : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ L (mixedDilCLE K).symm.toLinearMap

private theorem mem_mixedDilLattice (z : euclidean.mixedSpace K) :
    z ∈ mixedDilLattice K L ↔ (mixedDil K).symm z ∈ L :=
  Iff.rfl

private theorem mem_comap_mixedDil (N : Submodule ℤ (euclidean.mixedSpace K)) (z : euclidean.mixedSpace K) :
    z ∈ ZLattice.comap ℝ N (mixedDilCLE K).toLinearMap ↔ mixedDil K z ∈ N :=
  Iff.rfl

private theorem dualSubmodule_mixedDilLattice :
    LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) (mixedDilLattice K L)
      = ZLattice.comap ℝ
          (LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) L)
          (mixedDilCLE K).toLinearMap := by
  ext y
  rw [LinearMap.BilinForm.mem_dualSubmodule, mem_comap_mixedDil,
    LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro h w hw
    have hz : mixedDil K w ∈ mixedDilLattice K L := by
      rw [mem_mixedDilLattice]
      simpa using hw
    have h1 := h _ hz
    rw [innerₗ_apply_apply] at h1 ⊢
    rw [inner_mixedDil K y w]
    exact h1
  · intro h z hz
    rw [mem_mixedDilLattice] at hz
    have h1 := h _ hz
    rw [innerₗ_apply_apply] at h1 ⊢
    have hzz : z = mixedDil K ((mixedDil K).symm z) := by simp
    rw [hzz, ← inner_mixedDil K y ((mixedDil K).symm z)]
    exact h1

set_option maxHeartbeats 3200000 in

private theorem covolume_mixedDilLattice :
    ZLattice.covolume (mixedDilLattice K L) volume = 2 ^ nrComplexPlaces K * ZLattice.covolume L volume := by
  classical
  let b : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let bJ : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ (mixedDilLattice K L) :=
    b.ofZLatticeComap ℝ L (mixedDilCLE K).symm.toLinearEquiv
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Fintype.card (index K) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (↥L)]
    rw [show Module.finrank ℤ (↥L) = Module.finrank ℝ (euclidean.mixedSpace K) from ZLattice.rank ℝ L]
    rw [Module.finrank_eq_card_basis (euclidean.stdOrthonormalBasis K).toBasis]
  let e' : Module.Free.ChooseBasisIndex ℤ L ≃ index K := Fintype.equivOfCardEq hcard
  let o : OrthonormalBasis (Module.Free.ChooseBasisIndex ℤ L) ℝ (euclidean.mixedSpace K) :=
    (euclidean.stdOrthonormalBasis K).reindex e'.symm
  have hrepr : ∀ (x : euclidean.mixedSpace K) i,
      o.repr x i = (euclidean.stdOrthonormalBasis K).repr x (e' i) := by
    intro x i
    rw [show o = (euclidean.stdOrthonormalBasis K).reindex e'.symm from rfl,
      OrthonormalBasis.repr_reindex]
    simp
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped (b := o.toBasis) volume)]
    rw [measureReal_def,
      show parallelepiped ⇑(o.toBasis) = parallelepiped ⇑o from by rw [OrthonormalBasis.coe_toBasis],
      o.volume_parallelepiped]
    exact ENNReal.toReal_one
  have hbJcoe : ∀ k, ((bJ k : mixedDilLattice K L) : euclidean.mixedSpace K)
      = mixedDil K ((b k : L) : _) := by
    intro k
    rw [show bJ = b.ofZLatticeComap ℝ L (mixedDilCLE K).symm.toLinearEquiv from rfl]
    rw [Module.Basis.ofZLatticeComap_apply]
    simp [mixedDilCLE]
  have hmat : o.toBasis.toMatrix (fun k => ((bJ k : _) : euclidean.mixedSpace K))
      = Matrix.diagonal (fun i => dilDiag K (e' i))
          * o.toBasis.toMatrix (fun k => ((b k : L) : _)) := by
    ext i k
    rw [Matrix.diagonal_mul, Basis.toMatrix_apply, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis_repr_apply, hrepr, hrepr,
      hbJcoe, euclideanRepr_mixedDil]
  have hdet : o.toBasis.det (fun k => ((bJ k : _) : euclidean.mixedSpace K))
      = 2 ^ nrComplexPlaces K * o.toBasis.det (fun k => ((b k : L) : _)) := by
    rw [Basis.det_apply, Basis.det_apply, hmat, Matrix.det_mul, Matrix.det_diagonal]
    congr 1
    rw [Equiv.prod_comp e' (dilDiag K)]
    exact prod_dilDiag K
  have hJL : ZLattice.covolume (mixedDilLattice K L) volume
      = |o.toBasis.det (fun k => ((bJ k : _) : euclidean.mixedSpace K))| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal (b := bJ) (b₀ := o.toBasis) (μ := volume), hvol, mul_one]
    rfl
  have hL : ZLattice.covolume L volume = |o.toBasis.det (fun k => ((b k : L) : _))| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal (b := b) (b₀ := o.toBasis) (μ := volume), hvol, mul_one]
    rfl
  rw [hJL, hdet, abs_mul, hL, abs_of_pos (by positivity)]

private theorem covolume_mixedDilLattice_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (mixedDilLattice K (euclideanIdealLattice K I)) volume
      = (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * Real.sqrt |(discr K : ℝ)| := by
  rw [covolume_mixedDilLattice, covolume_euclideanIdealLattice]
  have h2 : (2 : ℝ) ^ nrComplexPlaces K * (2⁻¹) ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]; norm_num
  calc (2 : ℝ) ^ nrComplexPlaces K * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
        * (2⁻¹) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)
      = (2 : ℝ) ^ nrComplexPlaces K * (2⁻¹) ^ nrComplexPlaces K
        * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * Real.sqrt |(discr K : ℝ)|) := by
        ring
    _ = _ := by rw [h2, one_mul]

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_HeckeDTheta
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_RayThetaDefs

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real NumberField NumberField.InfinitePlace Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

private def heckeForm (x : K) : ℝ :=
  (∑ v : {w : InfinitePlace K // IsReal w}, (v.1 x) ^ 2)
    + ∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (w.1 x) ^ 2

private def rayScale (𝔣 : Ideal (𝓞 K)) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
      * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
    ^ (-(1 : ℝ) / (Module.finrank ℚ K : ℝ))

variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

private def rayWeight (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : K) : ℂ :=
  if x = 0 then (if 𝔣 = ⊤ then 1 else 0)
  else chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))

private def rayDualIdeal (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  dualIdealUnit K (Units.mk0 ((𝔣 : FractionalIdeal (𝓞 K)⁰ K)) (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣) * 𝔞)

private theorem rayScale_pos (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : 0 < rayScale K 𝔣 𝔞 := by
  unfold rayScale
  refine Real.rpow_pos_of_pos (mul_pos (mul_pos (abs_discr_pos K) ?_) (pow_pos (absNorm_units_pos K 𝔞) 2)) _
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h𝔣)

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_RayThetaDefs
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_RayThetaBuild

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

section H1
open NumberField.mixedEmbedding

private def idealPointEquiv (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≃ euclideanIdealLattice K 𝔞 :=
  Equiv.ofBijective
    (fun y => ⟨(euclidean.toMixed K).symm (mixedEmbedding K (y : K)),
      (mem_euclideanIdealLattice K 𝔞 _).mpr ⟨y, y.2, rfl⟩⟩)
    ⟨fun y y' h => by
        have h1 := congrArg Subtype.val h
        exact Subtype.ext (mixedEmbedding_injective K ((euclidean.toMixed K).symm.injective h1)),
     fun v => by
        obtain ⟨y, hy, hv⟩ := (mem_euclideanIdealLattice K 𝔞 (v : euclidean.mixedSpace K)).mp v.2
        exact ⟨⟨y, hy⟩, Subtype.ext hv⟩⟩

private theorem idealPointEquiv_apply (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    ((idealPointEquiv K 𝔞 y : euclideanIdealLattice K 𝔞) : euclidean.mixedSpace K)
      = (euclidean.toMixed K).symm (mixedEmbedding K (y : K)) := rfl

private theorem _root_.M4aP2.toMixed_symm_fst (z : mixedSpace K) (v : {w : InfinitePlace K // IsReal w}) :
    ((euclidean.toMixed K).symm z).fst v = z.1 v := rfl

p2m_export "M4aP2" "toMixed_symm_fst"
private theorem _root_.M4aP2.toMixed_symm_snd (z : mixedSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    ((euclidean.toMixed K).symm z).snd w = z.2 w := rfl

p2m_export "M4aP2" "toMixed_symm_snd"
private theorem heckeForm_eq_norm_sq_mixedDil (x : K) :
    heckeForm K x = ‖mixedDil K ((euclidean.toMixed K).symm (mixedEmbedding K x))‖ ^ 2 := by
  rw [norm_sq_mixedDil, heckeForm]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [toMixed_symm_fst, mixedEmbedding_apply_isReal, ← norm_embedding_of_isReal v.2 x, Real.norm_eq_abs, sq_abs]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [toMixed_symm_snd, mixedEmbedding_apply_isComplex, Complex.normSq_eq_norm_sq, norm_embedding_eq]

private theorem mem_coprimeToModulus_top (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : I ∈ coprimeToModulus K ⊤ := by
  rw [mem_coprimeToModulus_iff]
  intro v hv
  exact absurd (top_le_iff.mp (Ideal.le_of_dvd hv)) v.isPrime.ne_top

end H1
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section F1

variable {K}

omit [NumberField K] in

private theorem signAt_mul (S : Finset {w : InfinitePlace K // IsReal w}) (x y : K) :
    signAt K S (x * y) = signAt K S x * signAt K S y := by
  unfold signAt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_mul, sign_mul, SignType.coe_mul, Int.cast_mul]

omit [NumberField K] in

private theorem signAt_mul_self (S : Finset {w : InfinitePlace K // IsReal w}) {x : K} (hx : x ≠ 0) :
    signAt K S x * signAt K S x = 1 := by
  unfold signAt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  have hne : embedding_of_isReal v.2 x ≠ 0 := (map_ne_zero _).mpr hx
  rcases lt_or_gt_of_ne hne with h | h
  · rw [sign_neg h]; norm_num
  · rw [sign_pos h]; norm_num

variable (K)

private abbrev prinFI (α : 𝓞 K) : FractionalIdeal (𝓞 K)⁰ K :=
  ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

private theorem prinFI_ne_zero {α : 𝓞 K} (hα : α ≠ 0) : prinFI K α ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
  exact hα

omit [NumberField K] in
private theorem prinFI_zero : prinFI K (0 : 𝓞 K) = 0 := by
  rw [prinFI, Ideal.span_singleton_eq_bot.mpr rfl, FractionalIdeal.coeIdeal_bot]

omit [NumberField K] in
private theorem prinFI_mul (α β : 𝓞 K) : prinFI K (α * β) = prinFI K α * prinFI K β := by
  rw [prinFI, ← Ideal.span_singleton_mul_span_singleton, FractionalIdeal.coeIdeal_mul]

variable {K}
variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

private theorem chiIdeal_mul_of_mem {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hIc : Units.mk0 I hI ∈ coprimeToModulus K 𝔣) (hJc : Units.mk0 J hJ ∈ coprimeToModulus K 𝔣) :
    chiIdeal K 𝔣 χ (I * J) = chiIdeal K 𝔣 χ I * chiIdeal K 𝔣 χ J := by
  have hIJ : I * J ≠ 0 := mul_ne_zero hI hJ
  have hmk : Units.mk0 (I * J) hIJ = Units.mk0 I hI * Units.mk0 J hJ := Units.ext rfl
  have hIJc : Units.mk0 (I * J) hIJ ∈ coprimeToModulus K 𝔣 := by
    rw [hmk]; exact mul_mem hIc hJc
  rw [chiIdeal, dif_pos hIJ, dif_pos hIJc, chiIdeal, dif_pos hI, dif_pos hIc, chiIdeal, dif_pos hJ, dif_pos hJc,
    ← map_mul, ← map_mul]
  congr 2
  exact Subtype.ext hmk

private theorem chiIdeal_ne_zero_of_mem {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (hIc : Units.mk0 I hI ∈ coprimeToModulus K 𝔣) : chiIdeal K 𝔣 χ I ≠ 0 := by
  rw [chiIdeal, dif_pos hI, dif_pos hIc]
  set g := NarrowRayClassGroup.mk K 𝔣 ⟨Units.mk0 I hI, hIc⟩
  intro h
  have : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at this
  exact zero_ne_one this

private theorem chiIdeal_eq_zero_of_not_mem {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (hIc : Units.mk0 I hI ∉ coprimeToModulus K 𝔣) : chiIdeal K 𝔣 χ I = 0 := by
  rw [chiIdeal, dif_pos hI, dif_neg hIc]

private theorem chiIdeal_zero : chiIdeal K 𝔣 χ 0 = 0 := by
  rw [chiIdeal, dif_neg (not_not.mpr rfl)]

private theorem prin_mem_coprime_of_mul {α δ : 𝓞 K} (hα : α ≠ 0) (hδ : δ ≠ 0)
    (h : Units.mk0 (prinFI K (α * δ)) (prinFI_ne_zero K (mul_ne_zero hα hδ)) ∈ coprimeToModulus K 𝔣) :
    Units.mk0 (prinFI K α) (prinFI_ne_zero K hα) ∈ coprimeToModulus K 𝔣 := by
  rw [mem_coprimeToModulus_iff] at h ⊢
  intro v hv
  have h2 := h v hv
  rw [Units.val_mk0, prinFI_mul,
    FractionalIdeal.count_mul K v (prinFI_ne_zero K hα) (prinFI_ne_zero K hδ)] at h2
  have ha : 0 ≤ FractionalIdeal.count K v (prinFI K α) := FractionalIdeal.count_coe_nonneg K v _
  have hd : 0 ≤ FractionalIdeal.count K v (prinFI K δ) := FractionalIdeal.count_coe_nonneg K v _
  rw [Units.val_mk0]
  linarith

private theorem prin_mem_coprime_of_sub_one_mem {γ : 𝓞 K} (hγ : γ ≠ 0) (h1 : γ - 1 ∈ 𝔣) :
    Units.mk0 (prinFI K γ) (prinFI_ne_zero K hγ) ∈ coprimeToModulus K 𝔣 := by
  have := principalUnit_mem_coprimeToModulus K hγ h1
  rw [mem_coprimeToModulus_iff] at this ⊢
  intro v hv
  rw [Units.val_mk0]
  have h := this v hv
  rwa [principalUnit_val] at h

private theorem chiFin_core (S : Finset {w : InfinitePlace K // IsReal w}) (hS : IsParity K 𝔣 χ S)
    (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) {α β : 𝓞 K} (h : α - β ∈ 𝔣) (hβ : β ≠ 0)
    (hβc : Units.mk0 (prinFI K β) (prinFI_ne_zero K hβ) ∈ coprimeToModulus K 𝔣) :
    chiFin K 𝔣 χ S α = chiFin K 𝔣 χ S β ∧
      ∃ hα : α ≠ 0, Units.mk0 (prinFI K α) (prinFI_ne_zero K hα) ∈ coprimeToModulus K 𝔣 := by

  obtain ⟨δ, hδ⟩ := exists_mul_sub_one_mem_of_counts_zero K h𝔣 hβ
    (fun v hv => by
      have := (mem_coprimeToModulus_iff K).mp hβc v hv
      rwa [Units.val_mk0] at this)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [mul_zero, zero_sub, neg_mem_iff] at hδ
    exact h𝔣' ((Ideal.eq_top_iff_one _).mpr hδ)
  have hαδ : α * δ - 1 ∈ 𝔣 := by
    have e : α * δ - 1 = (α - β) * δ + (β * δ - 1) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ h) hδ
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_sub, neg_mem_iff] at hαδ
    exact h𝔣' ((Ideal.eq_top_iff_one _).mpr hαδ)

  have hαδc := prin_mem_coprime_of_sub_one_mem (mul_ne_zero hα0 hδ0) hαδ
  have hβδc := prin_mem_coprime_of_sub_one_mem (mul_ne_zero hβ hδ0) hδ
  have hαc := prin_mem_coprime_of_mul hα0 hδ0 hαδc
  have hδc : Units.mk0 (prinFI K δ) (prinFI_ne_zero K hδ0) ∈ coprimeToModulus K 𝔣 := by
    have hδβ : Units.mk0 (prinFI K (δ * β)) (prinFI_ne_zero K (mul_ne_zero hδ0 hβ)) ∈ coprimeToModulus K 𝔣 := by
      convert hβδc using 2; rw [mul_comm]
    exact prin_mem_coprime_of_mul hδ0 hβ hδβ
  refine ⟨?_, hα0, hαc⟩

  have hPα := hS (α * δ) (mul_ne_zero hα0 hδ0) hαδ
  have hPβ := hS (β * δ) (mul_ne_zero hβ hδ0) hδ
  change chiIdeal K 𝔣 χ (prinFI K (α * δ)) = _ at hPα
  change chiIdeal K 𝔣 χ (prinFI K (β * δ)) = _ at hPβ
  rw [prinFI_mul, chiIdeal_mul_of_mem χ (prinFI_ne_zero K hα0) (prinFI_ne_zero K hδ0) hαc hδc] at hPα
  rw [prinFI_mul, chiIdeal_mul_of_mem χ (prinFI_ne_zero K hβ) (prinFI_ne_zero K hδ0) hβc hδc] at hPβ
  have cα : ((α * δ : 𝓞 K) : K) = (α : K) * (δ : K) := by push_cast; rfl
  have cβ : ((β * δ : 𝓞 K) : K) = (β : K) * (δ : K) := by push_cast; rfl
  rw [cα, signAt_mul] at hPα
  rw [cβ, signAt_mul] at hPβ
  have hD := chiIdeal_ne_zero_of_mem χ (prinFI_ne_zero K hδ0) hδc
  have sα := signAt_mul_self S (RingOfIntegers.coe_ne_zero_iff.mpr hα0 : (α : K) ≠ 0)
  have sβ := signAt_mul_self S (RingOfIntegers.coe_ne_zero_iff.mpr hβ : (β : K) ≠ 0)

  have key : chiIdeal K 𝔣 χ (prinFI K δ) * (chiFin K 𝔣 χ S α - chiFin K 𝔣 χ S β) = 0 := by
    unfold chiFin
    change chiIdeal K 𝔣 χ (prinFI K δ)
      * (chiIdeal K 𝔣 χ (prinFI K α) * signAt K S (α : K) - chiIdeal K 𝔣 χ (prinFI K β) * signAt K S (β : K)) = 0
    linear_combination (signAt K S (α : K)) * hPα - (signAt K S (β : K)) * hPβ
      + (signAt K S (δ : K)) * sα - (signAt K S (δ : K)) * sβ
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hD
  · exact sub_eq_zero.mp h0

private theorem chiFin_zero (S : Finset {w : InfinitePlace K // IsReal w}) : chiFin K 𝔣 χ S 0 = 0 := by
  unfold chiFin
  change chiIdeal K 𝔣 χ (prinFI K 0) * _ = 0
  rw [prinFI_zero, chiIdeal_zero, zero_mul]

private theorem chiFin_eq_zero_of_not_mem (S : Finset {w : InfinitePlace K // IsReal w}) {α : 𝓞 K} (hα : α ≠ 0)
    (hαc : Units.mk0 (prinFI K α) (prinFI_ne_zero K hα) ∉ coprimeToModulus K 𝔣) : chiFin K 𝔣 χ S α = 0 := by
  unfold chiFin
  change chiIdeal K 𝔣 χ (prinFI K α) * _ = 0
  rw [chiIdeal_eq_zero_of_not_mem χ (prinFI_ne_zero K hα) hαc, zero_mul]

variable (K 𝔣)

private theorem chiFin_congr_v2 (S : Finset {w : InfinitePlace K // IsReal w}) (hS : IsParity K 𝔣 χ S) (h𝔣' : 𝔣 ≠ ⊤)
    {α β : 𝓞 K} (h : α - β ∈ 𝔣) : chiFin K 𝔣 χ S α = chiFin K 𝔣 χ S β := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣
    rw [Ideal.mem_bot, sub_eq_zero] at h
    rw [h]
  have h' : β - α ∈ 𝔣 := by rw [← neg_sub]; exact neg_mem h
  by_cases hβ0 : β = 0
  · subst hβ0
    rw [chiFin_zero]
    by_cases hα0 : α = 0
    · rw [hα0, chiFin_zero]
    by_cases hαc : Units.mk0 (prinFI K α) (prinFI_ne_zero K hα0) ∈ coprimeToModulus K 𝔣
    · obtain ⟨_, hβ0, _⟩ := chiFin_core χ S hS h𝔣 h𝔣' h' hα0 hαc
      exact absurd rfl hβ0
    · exact chiFin_eq_zero_of_not_mem χ S hα0 hαc
  by_cases hβc : Units.mk0 (prinFI K β) (prinFI_ne_zero K hβ0) ∈ coprimeToModulus K 𝔣
  · exact (chiFin_core χ S hS h𝔣 h𝔣' h hβ0 hβc).1
  rw [chiFin_eq_zero_of_not_mem χ S hβ0 hβc]
  by_cases hα0 : α = 0
  · rw [hα0, chiFin_zero]
  by_cases hαc : Units.mk0 (prinFI K α) (prinFI_ne_zero K hα0) ∈ coprimeToModulus K 𝔣
  · obtain ⟨_, _, hβc'⟩ := chiFin_core χ S hS h𝔣 h𝔣' h' hα0 hαc
    exact absurd hβc' hβc
  · exact chiFin_eq_zero_of_not_mem χ S hα0 hαc

end F1
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section F5

variable {K}
variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

variable (K 𝔣)

end F5
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_RayThetaBuild
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_GaussBuild

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real NumberField NumberField.InfinitePlace Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

section Torsor

private abbrev diffFI : FractionalIdeal (𝓞 K)⁰ K :=
  ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

private abbrev datumFI (𝔣 : Ideal (𝓞 K)) (y : K) : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K

variable {K}
variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

private theorem diffFI_ne_zero : diffFI K ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact differentIdeal_ne_bot

private theorem diffFI_eq_inv_dual_one :
    diffFI K = (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹ :=
  coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)

private theorem datumFI_le_one (h𝔣 : 𝔣 ≠ ⊥) {y : K} (hy : IsGaussDatum K 𝔣 χ y) : datumFI K 𝔣 y ≤ 1 := by
  have h𝔣0 : (𝔣 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣
  have hyd : y ∈ FractionalIdeal.dual ℤ ℚ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual h𝔣0]
    intro a ha
    obtain ⟨α, hα, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hy.2.1 α hα
  have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ y ≤ FractionalIdeal.dual ℤ ℚ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hyd
  have hd0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  calc datumFI K 𝔣 y
      ≤ FractionalIdeal.dual ℤ ℚ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K :=
        mul_le_mul_left (mul_le_mul_left h1 _) _
    _ = 1 := by
        rw [FractionalIdeal.dual_mul_self ℤ ℚ h𝔣0, diffFI_eq_inv_dual_one, mul_inv_cancel₀ hd0]

private theorem datumFI_mem_coprime {y : K} (hy : IsGaussDatum K 𝔣 χ y) :
    ∃ h0 : datumFI K 𝔣 y ≠ 0, Units.mk0 (datumFI K 𝔣 y) h0 ∈ coprimeToModulus K 𝔣 := by
  have hne : chiIdeal K 𝔣 χ (datumFI K 𝔣 y) ≠ 0 := hy.2.2
  by_cases h0 : datumFI K 𝔣 y = 0
  · rw [h0, chiIdeal_zero χ] at hne
    exact absurd rfl hne
  by_cases hc : Units.mk0 (datumFI K 𝔣 y) h0 ∈ coprimeToModulus K 𝔣
  · exact ⟨h0, hc⟩
  · exact absurd (chiIdeal_eq_zero_of_not_mem χ h0 hc) hne

private theorem exists_mem_sub_one_mem_of_coprime (h𝔣 : 𝔣 ≠ ⊥) {I : FractionalIdeal (𝓞 K)⁰ K} (hI1 : I ≤ 1) (hI0 : I ≠ 0)
    (hIc : Units.mk0 I hI0 ∈ coprimeToModulus K 𝔣) : ∃ a : 𝓞 K, (a : K) ∈ I ∧ a - 1 ∈ 𝔣 := by
  obtain ⟨I₀, hI₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hI1
  have hI₀0 : I₀ ≠ ⊥ := by
    rintro rfl
    exact hI0 (by rw [← hI₀, FractionalIdeal.coeIdeal_bot])
  have hsup : I₀ ⊔ 𝔣 = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm𝔣 : 𝔣 ≤ m := le_trans le_sup_right hle
    have hmI : I₀ ≤ m := le_trans le_sup_left hle
    have hmbot : m ≠ ⊥ := fun h => h𝔣 (le_bot_iff.mp (h ▸ hm𝔣))
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨m, hm.isPrime, hmbot⟩
    have hvdvd : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.mpr hm𝔣
    have hvI : v.asIdeal ∣ I₀ := Ideal.dvd_iff_le.mpr hmI
    have hcnt := (mem_coprimeToModulus_iff K).mp hIc v hvdvd
    rw [Units.val_mk0, ← hI₀, FractionalIdeal.count_coe K v (show I₀ ≠ 0 from hI₀0)] at hcnt
    have hz : (Associates.mk v.asIdeal).count (Associates.mk I₀).factors = 0 := by exact_mod_cast hcnt
    exact ((Associates.count_ne_zero_iff_dvd (show I₀ ≠ 0 from hI₀0) v.irreducible).mpr hvI) hz
  have h1 : (1 : 𝓞 K) ∈ I₀ ⊔ 𝔣 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, ha, f, hf, haf⟩ := Submodule.mem_sup.mp h1
  refine ⟨a, ?_, ?_⟩
  · rw [← hI₀, FractionalIdeal.mem_coeIdeal]
    exact ⟨a, ha, rfl⟩
  · have : a - 1 = -f := by linear_combination haf
    rw [this]
    exact neg_mem hf

private theorem exists_torsor_transport (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) {y y' : K}
    (hy : IsGaussDatum K 𝔣 χ y) (hy' : IsGaussDatum K 𝔣 χ y') :
    ∃ a c : 𝓞 K, a ≠ 0 ∧ a - 1 ∈ 𝔣 ∧ y' * (a : K) = (c : K) * y ∧
      prinFI K c * datumFI K 𝔣 y = datumFI K 𝔣 y' * prinFI K a ∧
      ∃ hc : c ≠ 0, Units.mk0 (prinFI K c) (prinFI_ne_zero K hc) ∈ coprimeToModulus K 𝔣 := by
  have hy0 : y ≠ 0 := hy.1
  have hy'0 : y' ≠ 0 := hy'.1
  obtain ⟨hU0, hUc⟩ := datumFI_mem_coprime χ hy
  obtain ⟨hU'0, hU'c⟩ := datumFI_mem_coprime χ hy'

  obtain ⟨a, haI, ha1⟩ := exists_mem_sub_one_mem_of_coprime h𝔣 (datumFI_le_one χ h𝔣 hy) hU0 hUc

  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_sub, neg_mem_iff] at ha1
    exact h𝔣' ((Ideal.eq_top_iff_one _).mpr ha1)

  have hay : y⁻¹ * (a : K) ∈ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K := by
    have h := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ y⁻¹) haI
    have e : FractionalIdeal.spanSingleton (𝓞 K)⁰ y⁻¹ * datumFI K 𝔣 y
        = (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K := by
      rw [datumFI, ← mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hy0,
        FractionalIdeal.spanSingleton_one, one_mul]
    rwa [e] at h
  have hc₀ : y' * (y⁻¹ * (a : K)) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ y') hay
    rw [← mul_assoc] at h
    exact datumFI_le_one χ h𝔣 hy' h
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).mp hc₀
  have hcK : (c : K) = y' * (y⁻¹ * (a : K)) := hc
  have hrel : y' * (a : K) = (c : K) * y := by
    rw [hcK]; field_simp
  have haK : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha0
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, show ((0 : 𝓞 K) : K) = 0 from map_zero (algebraMap (𝓞 K) K), zero_mul] at hrel
    exact (mul_ne_zero hy'0 haK) hrel

  have hval : prinFI K c * datumFI K 𝔣 y = datumFI K 𝔣 y' * prinFI K a := by
    rw [prinFI, prinFI, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton, datumFI, datumFI]
    have e1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) c) * FractionalIdeal.spanSingleton (𝓞 K)⁰ y
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ y' * FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) a) := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ← hrel, mul_comm]
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) c)
          * (FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K)
        = (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) c) * FractionalIdeal.spanSingleton (𝓞 K)⁰ y)
          * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K := by ring
      _ = (FractionalIdeal.spanSingleton (𝓞 K)⁰ y' * FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) a))
          * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K := by rw [e1]
      _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ y' * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K
          * FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) a) := by ring
  refine ⟨a, c, ha0, ha1, hrel, hval, hc0, ?_⟩

  have hAc := prin_mem_coprime_of_sub_one_mem (𝔣 := 𝔣) ha0 ha1
  have key : Units.mk0 (prinFI K c) (prinFI_ne_zero K hc0)
      = Units.mk0 (datumFI K 𝔣 y') hU'0 * Units.mk0 (prinFI K a) (prinFI_ne_zero K ha0)
          * (Units.mk0 (datumFI K 𝔣 y) hU0)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact Units.ext (by simp only [Units.val_mul, Units.val_mk0]; exact hval)
  rw [key]
  exact mul_mem (mul_mem hU'c hAc) (inv_mem hUc)

end Torsor
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section F2

variable {K}
variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

private theorem addChar_add (x z : K) : addChar K (x + z) = addChar K x * addChar K z := by
  unfold addChar
  rw [map_add, ← Complex.exp_add]
  push_cast
  ring_nf

private theorem addChar_eq_one_of_trace {x : K} (h : (Algebra.trace ℚ K x : ℚ) ∈ (algebraMap ℤ ℚ).range) : addChar K x = 1 := by
  obtain ⟨n, hn⟩ := h
  unfold addChar
  rw [← hn, eq_intCast, Rat.cast_intCast,
    show (2 * π * Complex.I * (n : ℂ) : ℂ) = n * (2 * π * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

private theorem chiFin_mul (S : Finset {w : InfinitePlace K // IsReal w}) (α β : 𝓞 K) :
    chiFin K 𝔣 χ S (α * β) = chiFin K 𝔣 χ S α * chiFin K 𝔣 χ S β := by
  by_cases hα : α = 0
  · rw [hα, zero_mul, chiFin_zero, zero_mul]
  by_cases hβ : β = 0
  · rw [hβ, mul_zero, chiFin_zero, mul_zero]
  by_cases hαc : Units.mk0 (prinFI K α) (prinFI_ne_zero K hα) ∈ coprimeToModulus K 𝔣
  · by_cases hβc : Units.mk0 (prinFI K β) (prinFI_ne_zero K hβ) ∈ coprimeToModulus K 𝔣
    · unfold chiFin
      change chiIdeal K 𝔣 χ (prinFI K (α * β)) * _ = chiIdeal K 𝔣 χ (prinFI K α) * _ * (chiIdeal K 𝔣 χ (prinFI K β) * _)
      rw [prinFI_mul, chiIdeal_mul_of_mem χ (prinFI_ne_zero K hα) (prinFI_ne_zero K hβ) hαc hβc,
        show ((α * β : 𝓞 K) : K) = (α : K) * (β : K) from map_mul (algebraMap (𝓞 K) K) α β, signAt_mul]
      ring
    · rw [chiFin_eq_zero_of_not_mem χ S hβ hβc, mul_zero]
      refine chiFin_eq_zero_of_not_mem χ S (mul_ne_zero hα hβ) fun h => hβc ?_
      exact prin_mem_coprime_of_mul hβ hα (by simpa only [mul_comm α β] using h)
  · rw [chiFin_eq_zero_of_not_mem χ S hα hαc, zero_mul]
    exact chiFin_eq_zero_of_not_mem χ S (mul_ne_zero hα hβ) fun h => hαc (prin_mem_coprime_of_mul hα hβ h)

private def gaussCore (h𝔣 : 𝔣 ≠ ⊥) (S : Finset {w : InfinitePlace K // IsReal w}) (y : K) : ℂ :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  haveI : Fintype (𝓞 K ⧸ 𝔣) := Fintype.ofFinite _
  ∑ r : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out r) * addChar K ((Quotient.out r : 𝓞 K) * y)

private theorem gaussSumAt_eq_mul_gaussCore (h𝔣 : 𝔣 ≠ ⊥) (S : Finset {w : InfinitePlace K // IsReal w}) (y : K) :
    gaussSumAt K 𝔣 χ h𝔣 S y = signAt K S y * chiIdeal K 𝔣 χ (datumFI K 𝔣 y) * gaussCore χ h𝔣 S y := rfl

private theorem gaussCore_congr (h𝔣 : 𝔣 ≠ ⊥) (S : Finset {w : InfinitePlace K // IsReal w}) {y z : K}
    (h : ∀ β : 𝓞 K, addChar K ((β : K) * y) = addChar K ((β : K) * z)) : gaussCore χ h𝔣 S y = gaussCore χ h𝔣 S z := by
  unfold gaussCore
  exact Finset.sum_congr rfl fun r _ => by rw [h]

private theorem addChar_mul_datum_eq {y' : K} (hy' : IsGaussDatum K 𝔣 χ y') {a : 𝓞 K} (ha1 : a - 1 ∈ 𝔣) (β : 𝓞 K) :
    addChar K ((β : K) * y') = addChar K ((β : K) * (y' * (a : K))) := by
  have hmem : β * (1 - a) ∈ 𝔣 := by
    refine Ideal.mul_mem_left _ _ ?_
    rw [← neg_sub]
    exact neg_mem ha1
  have h1 := addChar_eq_one_of_trace (hy'.2.1 _ hmem)
  have e : (β : K) * y' = (β : K) * (y' * (a : K)) + ((β * (1 - a) : 𝓞 K) : K) * y' := by
    push_cast
    ring
  rw [e, addChar_add, h1, mul_one]

private theorem isUnit_mk_of_coprime (h𝔣 : 𝔣 ≠ ⊥) {c : 𝓞 K} (hc : c ≠ 0)
    (hcc : Units.mk0 (prinFI K c) (prinFI_ne_zero K hc) ∈ coprimeToModulus K 𝔣) : IsUnit (Ideal.Quotient.mk 𝔣 c) := by
  obtain ⟨d, hd⟩ := exists_mul_sub_one_mem_of_counts_zero K h𝔣 hc
    (fun v hv => by
      have := (mem_coprimeToModulus_iff K).mp hcc v hv
      rwa [Units.val_mk0] at this)
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔣 d) ?_
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔣), Ideal.Quotient.eq]
  exact hd

private theorem gaussCore_eq_chiFin_mul (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) (S : Finset {w : InfinitePlace K // IsReal w})
    (hS : IsParity K 𝔣 χ S) {y : K} (hy : ∀ g : 𝓞 K, g ∈ 𝔣 → addChar K ((g : K) * y) = 1) {c : 𝓞 K} (hc : c ≠ 0)
    (hcc : Units.mk0 (prinFI K c) (prinFI_ne_zero K hc) ∈ coprimeToModulus K 𝔣) :
    gaussCore χ h𝔣 S y = chiFin K 𝔣 χ S c * gaussCore χ h𝔣 S ((c : K) * y) := by
  obtain ⟨u, hu⟩ := isUnit_mk_of_coprime h𝔣 hc hcc
  letI := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  letI : Fintype (𝓞 K ⧸ 𝔣) := Fintype.ofFinite _
  unfold gaussCore
  rw [Finset.mul_sum]

  refine (Fintype.sum_equiv (Units.mulRight u) _ _ fun s => ?_).symm
  rw [Units.mulRight_apply]

  have hg : Quotient.out (s * (u : 𝓞 K ⧸ 𝔣)) - Quotient.out s * c ∈ 𝔣 := by
    rw [← Ideal.Quotient.eq, map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, hu]
  rw [chiFin_congr_v2 K 𝔣 χ S hS h𝔣' hg, chiFin_mul]

  have h1 := hy _ hg
  have e : ((Quotient.out (s * (u : 𝓞 K ⧸ 𝔣)) : 𝓞 K) : K) * y
      = ((Quotient.out s : 𝓞 K) : K) * ((c : K) * y)
        + (((Quotient.out (s * (u : 𝓞 K ⧸ 𝔣)) - Quotient.out s * c : 𝓞 K)) : K) * y := by
    push_cast
    ring
  rw [e, addChar_add, h1, mul_one]
  ring

private theorem prefactor_transport (S : Finset {w : InfinitePlace K // IsReal w}) (hS : IsParity K 𝔣 χ S) {y y' : K}
    (hy : IsGaussDatum K 𝔣 χ y) (hy' : IsGaussDatum K 𝔣 χ y') {a c : 𝓞 K} (ha0 : a ≠ 0) (ha1 : a - 1 ∈ 𝔣)
    (hrel : y' * (a : K) = (c : K) * y) (hval : prinFI K c * datumFI K 𝔣 y = datumFI K 𝔣 y' * prinFI K a)
    (hc : c ≠ 0) (hcc : Units.mk0 (prinFI K c) (prinFI_ne_zero K hc) ∈ coprimeToModulus K 𝔣) :
    signAt K S y' * chiIdeal K 𝔣 χ (datumFI K 𝔣 y')
      = chiFin K 𝔣 χ S c * (signAt K S y * chiIdeal K 𝔣 χ (datumFI K 𝔣 y)) := by
  obtain ⟨hU0, hUc⟩ := datumFI_mem_coprime χ hy
  obtain ⟨hU'0, hU'c⟩ := datumFI_mem_coprime χ hy'
  have hAc := prin_mem_coprime_of_sub_one_mem (𝔣 := 𝔣) ha0 ha1

  have E1 : chiIdeal K 𝔣 χ (datumFI K 𝔣 y') * chiIdeal K 𝔣 χ (prinFI K a)
      = chiIdeal K 𝔣 χ (prinFI K c) * chiIdeal K 𝔣 χ (datumFI K 𝔣 y) := by
    rw [← chiIdeal_mul_of_mem χ hU'0 (prinFI_ne_zero K ha0) hU'c hAc,
      ← chiIdeal_mul_of_mem χ (prinFI_ne_zero K hc) hU0 hcc hUc, hval]

  have E2 : chiIdeal K 𝔣 χ (prinFI K a) = signAt K S (a : K) := hS a ha0 ha1

  have E3 : signAt K S y' * signAt K S (a : K) = signAt K S (c : K) * signAt K S y := by
    rw [← signAt_mul, ← signAt_mul, hrel]

  have E4 := signAt_mul_self S (RingOfIntegers.coe_ne_zero_iff.mpr ha0 : (a : K) ≠ 0)
  unfold chiFin
  change _ = chiIdeal K 𝔣 χ (prinFI K c) * signAt K S (c : K) * _
  linear_combination (-(signAt K S y' * chiIdeal K 𝔣 χ (datumFI K 𝔣 y'))) * E4
    + (signAt K S (c : K) * signAt K S y) * E1
    - (signAt K S (c : K) * signAt K S y * chiIdeal K 𝔣 χ (datumFI K 𝔣 y')) * E2
    + (chiIdeal K 𝔣 χ (datumFI K 𝔣 y') * signAt K S (a : K)) * E3

private theorem gaussCore_top {h𝔣 : (⊤ : Ideal (𝓞 K)) ≠ ⊥} (χT : NarrowRayClassGroup K ⊤ →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) {y y' : K}
    (hy : IsGaussDatum K ⊤ χT y) (hy' : IsGaussDatum K ⊤ χT y') : gaussCore χT h𝔣 S y = gaussCore χT h𝔣 S y' := by
  refine gaussCore_congr χT h𝔣 S fun β => ?_
  rw [addChar_eq_one_of_trace (hy.2.1 β Submodule.mem_top), addChar_eq_one_of_trace (hy'.2.1 β Submodule.mem_top)]

private theorem mem_coprime_top (U : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : U ∈ coprimeToModulus K (⊤ : Ideal (𝓞 K)) := by
  rw [coprimeToModulus_top]; exact Subgroup.mem_top U

private theorem prefactor_top (χT : NarrowRayClassGroup K ⊤ →* ℂ) (S : Finset {w : InfinitePlace K // IsReal w})
    (hS : IsParity K ⊤ χT S) {y : K} (hy : y ≠ 0) :
    signAt K S y * chiIdeal K ⊤ χT (datumFI K ⊤ y) = chiIdeal K ⊤ χT (diffFI K) := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : (d : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd0
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hy
    rw [← hnd, map_zero, zero_div]
  have hnK : (n : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hn0
  change (n : K) / (d : K) = y at hnd

  have htop : ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1 := FractionalIdeal.coeIdeal_top _
  have hD : datumFI K ⊤ y = FractionalIdeal.spanSingleton (𝓞 K)⁰ y * diffFI K := by
    rw [datumFI, htop, mul_one]
  have hDd : datumFI K ⊤ y * prinFI K d = prinFI K n * diffFI K := by
    rw [hD, prinFI, prinFI, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      mul_right_comm, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 2
    rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ← hnd, div_mul_cancel₀ _ hdK]
  have hy0' : FractionalIdeal.spanSingleton (𝓞 K)⁰ y ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy
  have hD0 : datumFI K ⊤ y ≠ 0 := by rw [hD]; exact mul_ne_zero hy0' diffFI_ne_zero

  have E1 : chiIdeal K ⊤ χT (datumFI K ⊤ y) * chiIdeal K ⊤ χT (prinFI K d)
      = chiIdeal K ⊤ χT (prinFI K n) * chiIdeal K ⊤ χT (diffFI K) := by
    rw [← chiIdeal_mul_of_mem χT hD0 (prinFI_ne_zero K hd0) (mem_coprime_top _) (mem_coprime_top _),
      ← chiIdeal_mul_of_mem χT (prinFI_ne_zero K hn0) diffFI_ne_zero (mem_coprime_top _) (mem_coprime_top _), hDd]
  have E2 : chiIdeal K ⊤ χT (prinFI K n) = signAt K S (n : K) := hS n hn0 Submodule.mem_top
  have E3 : chiIdeal K ⊤ χT (prinFI K d) = signAt K S (d : K) := hS d hd0 Submodule.mem_top
  have E4 : signAt K S y * signAt K S (d : K) = signAt K S (n : K) := by
    rw [← signAt_mul, ← hnd, div_mul_cancel₀ _ hdK]
  have E5 := signAt_mul_self S hnK
  have E6 := signAt_mul_self S hdK
  linear_combination (-(signAt K S y * chiIdeal K ⊤ χT (datumFI K ⊤ y))) * E6
    + (-(signAt K S y * signAt K S (d : K) * chiIdeal K ⊤ χT (datumFI K ⊤ y))) * E3
    + (signAt K S y * signAt K S (d : K)) * E1
    + (chiIdeal K ⊤ χT (prinFI K n) * chiIdeal K ⊤ χT (diffFI K)) * E4
    + (signAt K S (n : K) * chiIdeal K ⊤ χT (diffFI K)) * E2
    + (chiIdeal K ⊤ χT (diffFI K)) * E5

variable (K 𝔣)

private theorem gaussSumAt_indep (S : Finset {w : InfinitePlace K // IsReal w}) (hS : IsParity K 𝔣 χ S)
    (h𝔣 : 𝔣 ≠ ⊥) {y y' : K} (hy : IsGaussDatum K 𝔣 χ y) (hy' : IsGaussDatum K 𝔣 χ y') :
    gaussSumAt K 𝔣 χ h𝔣 S y = gaussSumAt K 𝔣 χ h𝔣 S y' := by
  rw [gaussSumAt_eq_mul_gaussCore, gaussSumAt_eq_mul_gaussCore]
  by_cases h𝔣' : 𝔣 = ⊤
  ·
    subst h𝔣'
    rw [prefactor_top χ S hS hy.1, prefactor_top χ S hS hy'.1, gaussCore_top χ S hy hy']
  ·
    obtain ⟨a, c, ha0, ha1, hrel, hval, hc0, hcc⟩ := exists_torsor_transport χ h𝔣 h𝔣' hy hy'
    have hG : gaussCore χ h𝔣 S y = chiFin K 𝔣 χ S c * gaussCore χ h𝔣 S y' := by
      rw [gaussCore_eq_chiFin_mul χ h𝔣 h𝔣' S hS (fun g hg => addChar_eq_one_of_trace (hy.2.1 g hg)) hc0 hcc, ← hrel]
      congr 1
      exact (gaussCore_congr χ h𝔣 S (addChar_mul_datum_eq χ hy' ha1)).symm
    rw [hG, prefactor_transport χ S hS hy hy' ha0 ha1 hrel hval hc0 hcc]
    ring

end F2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section F3

variable {K}
variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

private theorem trace_mem_of_addChar_eq_one {x : K} (h : addChar K x = 1) :
    (Algebra.trace ℚ K x : ℚ) ∈ (algebraMap ℤ ℚ).range := by
  unfold addChar at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : ((Algebra.trace ℚ K x : ℚ) : ℂ) = (n : ℂ) := by
    have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_right_cancel₀ hπ (show ((Algebra.trace ℚ K x : ℚ) : ℂ) * (2 * π * Complex.I) = n * (2 * π * Complex.I) by
      rw [← hn]; ring)
    exact this
  refine ⟨n, ?_⟩
  rw [eq_intCast]
  exact_mod_cast h2.symm

private theorem norm_chiIdeal_of_mem (h𝔣 : 𝔣 ≠ ⊥) {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (hIc : Units.mk0 I hI ∈ coprimeToModulus K 𝔣) : ‖chiIdeal K 𝔣 χ I‖ = 1 := by
  haveI := Deep.NTSupply.finite K h𝔣
  rw [chiIdeal, dif_pos hI, dif_pos hIc]
  set g := NarrowRayClassGroup.mk K 𝔣 ⟨Units.mk0 I hI, hIc⟩
  have hfin : IsOfFinOrder (χ g) := χ.isOfFinOrder (isOfFinOrder_of_finite g)
  exact Complex.norm_eq_one_of_pow_eq_one (pow_orderOf_eq_one (χ g)) hfin.orderOf_pos.ne'

private theorem normSq_chiIdeal_of_mem (h𝔣 : 𝔣 ≠ ⊥) {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (hIc : Units.mk0 I hI ∈ coprimeToModulus K 𝔣) : Complex.normSq (chiIdeal K 𝔣 χ I) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_chiIdeal_of_mem χ h𝔣 hI hIc, one_pow]

omit [NumberField K] in

private theorem normSq_signAt (S : Finset {w : InfinitePlace K // IsReal w}) {x : K} (hx : x ≠ 0) :
    Complex.normSq (signAt K S x) = 1 := by
  unfold signAt
  rw [Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_eq_one, one_pow]
  intro v _
  have hne : embedding_of_isReal v.2 x ≠ 0 := (map_ne_zero _).mpr hx
  rcases lt_or_gt_of_ne hne with h | h
  · rw [sign_neg h]; norm_num
  · rw [sign_pos h]; norm_num

omit [NumberField K] in

private theorem signAt_eq_one_of_totallyPositive (S : Finset {w : InfinitePlace K // IsReal w}) {x : K}
    (hx : ∀ τ : K →+* ℝ, 0 < τ x) : signAt K S x = 1 := by
  unfold signAt
  refine Finset.prod_eq_one fun v _ => ?_
  rw [sign_pos (hx _)]; norm_num

variable (K 𝔣)

end F3
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_GaussBuild
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTorus_ChiFinOrth

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
namespace ChiFinOrth
p2m_open "M4aTorus"

p2m_open "NumberField NumberField.InfinitePlace Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

private theorem ne_bot_of_fintype_quotient [Fintype (𝓞 K ⧸ 𝔣)] : 𝔣 ≠ ⊥ := by
  intro h
  subst h
  have hinj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal (𝓞 K))) := by
    intro x y hxy
    have := Ideal.Quotient.eq.mp hxy
    rwa [Ideal.mem_bot, sub_eq_zero] at this
  haveI : Finite (𝓞 K) := Finite.of_injective _ hinj
  exact not_finite (𝓞 K)

private theorem isUnit_mk_of_chiFin_ne_zero (S : Finset {w : InfinitePlace K // IsReal w}) (h𝔣 : 𝔣 ≠ ⊥) {α : 𝓞 K}
    (h : chiFin K 𝔣 χ S α ≠ 0) : IsUnit (Ideal.Quotient.mk 𝔣 α) := by
  have hα : α ≠ 0 := by
    rintro rfl
    exact h (chiFin_zero χ S)
  by_cases hαc : Units.mk0 (prinFI K α) (prinFI_ne_zero K hα) ∈ coprimeToModulus K 𝔣
  · exact isUnit_mk_of_coprime h𝔣 hα hαc
  · exact absurd (chiFin_eq_zero_of_not_mem χ S hα hαc) h

private theorem sum_chiFin_out_eq_zero [Fintype (𝓞 K ⧸ 𝔣)] (S : Finset {w : InfinitePlace K // IsReal w}) (hS : IsParity K 𝔣 χ S) (h𝔣' : 𝔣 ≠ ⊤)
    (hne : ∃ α : 𝓞 K, chiFin K 𝔣 χ S α ≠ 0 ∧ chiFin K 𝔣 χ S α ≠ 1) :
    ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a) = 0 := by
  have h𝔣 : 𝔣 ≠ ⊥ := ne_bot_of_fintype_quotient K
  obtain ⟨c, hc0, hc1⟩ := hne
  obtain ⟨u, hu⟩ := isUnit_mk_of_chiFin_ne_zero K χ S h𝔣 hc0
  have hkey : ∀ a : 𝓞 K ⧸ 𝔣,
      chiFin K 𝔣 χ S (Quotient.out ((u : 𝓞 K ⧸ 𝔣) * a)) = chiFin K 𝔣 χ S c * chiFin K 𝔣 χ S (Quotient.out a) := by
    intro a
    rw [← chiFin_mul]
    refine chiFin_congr_v2 K 𝔣 χ S hS h𝔣' ?_
    rw [← Ideal.Quotient.eq, map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, hu]
  have hsum : ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S c * chiFin K 𝔣 χ S (Quotient.out a)
      = ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a) :=
    Fintype.sum_equiv u.mulLeft _ _ fun a => by
      show _ = chiFin K 𝔣 χ S (Quotient.out ((u : 𝓞 K ⧸ 𝔣) * a))
      exact (hkey a).symm
  rw [← Finset.mul_sum] at hsum
  have h0 : (chiFin K 𝔣 χ S c - 1) * ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a) = 0 := by
    rw [sub_mul, one_mul, hsum, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h

end M4aTorus.ChiFinOrth
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTorus_ChiFinOrth
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_TranslatedTheta

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

p2m_open "Real MeasureTheory Set Function Topology Module Complex Function.Complex"
open TopologicalSpace (Compacts)
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private def translatedGaussianMap (t : ℝ) (v₀ : E) : C(E, ℂ) :=
  (gaussianMap t).comp (ContinuousMap.addRight v₀)

private theorem translatedGaussian_translateNorm_summable {t : ℝ} (ht : 0 < t)
    (v₀ : E) (K : Compacts E) :
    Summable fun v : L =>
      ‖((translatedGaussianMap t v₀).comp
          (ContinuousMap.addRight (v : E))).restrict (K : Set E)‖ := by
  have hbig := gaussian_translateNorm_summable (E := E) L ht
    (K.map (fun y => y + v₀) (continuous_add_const v₀))
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hbig
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  rintro ⟨x, hx⟩
  have hmem : x + v₀ ∈ (K.map (fun y => y + v₀) (continuous_add_const v₀) : Set E) :=
    ⟨x, hx, rfl⟩
  calc ‖((translatedGaussianMap t v₀).comp
        (ContinuousMap.addRight (v : E))).restrict (K : Set E) ⟨x, hx⟩‖
      = ‖gaussianMap t ((x + (v : E)) + v₀)‖ := rfl
    _ = ‖gaussianMap t ((x + v₀) + (v : E))‖ := by rw [add_right_comm]
    _ = ‖((gaussianMap t).comp
          (ContinuousMap.addRight (v : E))).restrict
            (K.map (fun y => y + v₀) (continuous_add_const v₀) : Set E) ⟨x + v₀, hmem⟩‖ := rfl
    _ ≤ _ := ContinuousMap.norm_coe_le_norm _ _

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_TranslatedTheta
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_WeightedCoset

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

p2m_open "Real MeasureTheory Set Function Topology Module Complex Function.Complex"
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_WeightedCoset
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_CosetPartition

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

p2m_open "Real MeasureTheory Set Function Topology Module Complex Function.Complex"
open TopologicalSpace (Compacts)
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

section Abstract

variable {α : Type} [AddCommGroup α] (H : AddSubgroup α)

private theorem tsum_partition_quotient {f : α → ℂ} (hf : Summable f) :
    ∑' v : α, f v
      = ∑' c : α ⧸ H, ∑' v : (QuotientAddGroup.mk ⁻¹' {c} : Set α), f v := by
  rw [← (Equiv.sigmaFiberEquiv
    (QuotientAddGroup.mk (s := H) : α → α ⧸ H)).tsum_eq f]
  exact ((Equiv.sigmaFiberEquiv _).summable_iff.mpr hf).tsum_sigma

private def fiberShiftEquiv (c : α ⧸ H) (r : α)
    (hr : (QuotientAddGroup.mk r : α ⧸ H) = c) :
    (H : Type _) ≃ (QuotientAddGroup.mk ⁻¹' {c} : Set α) where
  toFun u := ⟨(u : α) + r, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [show (QuotientAddGroup.mk ((u : α) + r) : α ⧸ H)
        = QuotientAddGroup.mk r from QuotientAddGroup.eq.mpr (by
      have h : -((u : α) + r) + r = -(u : α) := by abel
      rw [h]; exact H.neg_mem u.2), hr]⟩
  invFun v := ⟨(v : α) - r, by
    have hv : (QuotientAddGroup.mk (v : α) : α ⧸ H) = c := v.2
    have hm := QuotientAddGroup.eq.mp (hr.trans hv.symm)
    have h : -r + (v : α) = (v : α) - r := by abel
    rwa [h] at hm⟩
  left_inv u := by ext; simp
  right_inv v := by ext; simp

private theorem tsum_fiber_eq_tsum_translate {f : α → ℂ} (c : α ⧸ H) (r : α)
    (hr : (QuotientAddGroup.mk r : α ⧸ H) = c) :
    ∑' v : (QuotientAddGroup.mk ⁻¹' {c} : Set α), f v
      = ∑' u : H, f ((u : α) + r) :=
  ((fiberShiftEquiv H c r hr).tsum_eq fun v => f (v : α)).symm

end Abstract
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_CosetPartition
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_OddGaussian

set_option maxHeartbeats 4000000

open Real MeasureTheory Complex
open scoped FourierTransform

noncomputable section

namespace Deep
p2m_export "Deep" "NTSupply.finite Analytic.euclideanIdealLattice"
namespace Analytic
p2m_export "Deep.Analytic" "euclideanIdealLattice"
p2m_open "Deep.Analytic Deep"

end Deep.Analytic
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_OddGaussian
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_OddCoset

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real Complex MeasureTheory Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
open scoped FourierTransform InnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private def oddConst (t : ℝ) (j : ℕ) : ℝ := 1 + (j.factorial : ℝ) / (π * t / 2) ^ j

private theorem oddConst_pos {t : ℝ} (ht : 0 < t) (j : ℕ) : 0 < oddConst t j := by
  unfold oddConst; positivity

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

private theorem norm_pow_mul_gaussian_le {t : ℝ} (ht : 0 < t) (j : ℕ) (v : E) :
    ‖v‖ ^ j * Real.exp (-π * t * ‖v‖ ^ 2) ≤ oddConst t j * Real.exp (-π * (t / 2) * ‖v‖ ^ 2) := by
  set a : ℝ := π * t / 2 with ha
  have ha0 : 0 < a := by positivity
  have hr : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ j ≤ 1 + (‖v‖ ^ 2) ^ j := by
    rcases le_or_gt ‖v‖ 1 with h | h
    · exact (pow_le_one₀ hr h).trans (le_add_of_nonneg_right (by positivity))
    · have : ‖v‖ ^ j ≤ ‖v‖ ^ (2 * j) := pow_le_pow_right₀ h.le (by omega)
      rw [pow_mul] at this
      exact this.trans (le_add_of_nonneg_left zero_le_one)
  have h2 : (‖v‖ ^ 2) ^ j ≤ (j.factorial : ℝ) / a ^ j * Real.exp (a * ‖v‖ ^ 2) := by
    have h := Real.pow_div_factorial_le_exp (x := a * ‖v‖ ^ 2) (by positivity) j
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc (‖v‖ ^ 2) ^ j * a ^ j = a ^ j * (‖v‖ ^ 2) ^ j := by ring
      _ ≤ Real.exp (a * ‖v‖ ^ 2) * j.factorial := h
      _ = (j.factorial : ℝ) * Real.exp (a * ‖v‖ ^ 2) := by ring
  have hexp : Real.exp (-π * t * ‖v‖ ^ 2) = Real.exp (-a * ‖v‖ ^ 2) * Real.exp (-a * ‖v‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; rw [ha]; ring
  have hhalf : Real.exp (-π * (t / 2) * ‖v‖ ^ 2) = Real.exp (-a * ‖v‖ ^ 2) := by
    congr 1; rw [ha]; ring
  have hE : 0 < Real.exp (-a * ‖v‖ ^ 2) := Real.exp_pos _
  have hle1 : Real.exp (-a * ‖v‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖v‖]
  rw [hhalf, show oddConst t j = 1 + (j.factorial : ℝ) / a ^ j from rfl]
  calc ‖v‖ ^ j * Real.exp (-π * t * ‖v‖ ^ 2)
      ≤ (1 + (j.factorial : ℝ) / a ^ j * Real.exp (a * ‖v‖ ^ 2))
          * (Real.exp (-a * ‖v‖ ^ 2) * Real.exp (-a * ‖v‖ ^ 2)) := by
        rw [hexp]; gcongr; exact h1.trans (by gcongr)
    _ = Real.exp (-a * ‖v‖ ^ 2) * Real.exp (-a * ‖v‖ ^ 2)
          + (j.factorial : ℝ) / a ^ j * Real.exp (-a * ‖v‖ ^ 2) := by
        have : Real.exp (a * ‖v‖ ^ 2) * Real.exp (-a * ‖v‖ ^ 2) = 1 := by
          rw [← Real.exp_add]; simp
        linear_combination (j.factorial : ℝ) / a ^ j * Real.exp (-a * ‖v‖ ^ 2) * this
    _ ≤ 1 * Real.exp (-a * ‖v‖ ^ 2) + (j.factorial : ℝ) / a ^ j * Real.exp (-a * ‖v‖ ^ 2) := by
        gcongr
    _ = (1 + (j.factorial : ℝ) / a ^ j) * Real.exp (-a * ‖v‖ ^ 2) := by ring

private theorem integrable_gaussianR {s : ℝ} (hs : 0 < s) : Integrable (fun v : E => Real.exp (-π * s * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := ((π * s : ℝ) : ℂ))
    (by simpa using mul_pos Real.pi_pos hs) 0 0
  refine (h.norm).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re]

private theorem integrable_norm_pow_mul_gaussian {t : ℝ} (ht : 0 < t) (j : ℕ) :
    Integrable (fun v : E => ‖v‖ ^ j * Real.exp (-π * t * ‖v‖ ^ 2)) := by
  refine ((integrable_gaussianR (half_pos ht)).const_mul (oddConst t j)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_pow_mul_gaussian_le ht j v

variable {σ : Type} (e : σ → E)

private def polyS (S : Finset σ) (x : E) : ℂ := ∏ u ∈ S, ((⟪e u, x⟫_ℝ : ℝ) : ℂ)

private def oddGaussian (t : ℝ) (S : Finset σ) (x : E) : ℂ := polyS e S x * gaussianMap t x

private def gaussFT (t : ℝ) (w : E) : ℂ :=
  (1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2) * Complex.exp (-(π : ℂ) / t * (‖w‖ : ℂ) ^ 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_polyS (S : Finset σ) : Continuous (polyS e S) := by
  unfold polyS
  exact continuous_finsetProd _ fun u _ => Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_oddGaussian (t : ℝ) (S : Finset σ) : Continuous (oddGaussian e t S) :=
  (continuous_polyS e S).mul (gaussianMap t).continuous

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_polyS_le (he : Orthonormal ℝ e) (S : Finset σ) (x : E) : ‖polyS e S x‖ ≤ ‖x‖ ^ S.card := by
  unfold polyS
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun u _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc |⟪e u, x⟫_ℝ| ≤ ‖e u‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ = ‖x‖ := by rw [he.norm_eq_one u, one_mul]

private theorem norm_oddGaussian_le (he : Orthonormal ℝ e) (t : ℝ) (S : Finset σ) (x : E) :
    ‖oddGaussian e t S x‖ ≤ ‖x‖ ^ S.card * Real.exp (-π * t * ‖x‖ ^ 2) := by
  unfold oddGaussian
  rw [norm_mul, norm_gaussianMap]
  exact mul_le_mul_of_nonneg_right (norm_polyS_le e he S x) (Real.exp_pos _).le

private theorem integrable_oddGaussian (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ) :
    Integrable (oddGaussian e t S) :=
  (integrable_norm_pow_mul_gaussian ht S.card).mono' (continuous_oddGaussian e t S).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_oddGaussian_le e he t S))

private theorem integrable_norm_mul_oddGaussian (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ) :
    Integrable (fun v : E => ‖v‖ * ‖oddGaussian e t S v‖) := by
  refine (integrable_norm_pow_mul_gaussian ht (S.card + 1)).mono'
    (continuous_norm.mul (continuous_oddGaussian e t S).norm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_succ']
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_oddGaussian_le e he t S v) (norm_nonneg _)

private theorem fourier_inner_mul_of_hasFDerivAt {f : E → ℂ} (hint : Integrable f)
    (hint' : Integrable (fun v : E => ‖v‖ * ‖f v‖)) {F : E → ℂ} (hF : 𝓕 f = F)
    {w : E} {Fd : E →L[ℝ] ℂ} (hFd : HasFDerivAt F Fd w) (a : E) :
    𝓕 (fun v : E => ((⟪a, v⟫_ℝ : ℝ) : ℂ) * f v) w = (-(2 * π * Complex.I))⁻¹ * Fd a := by
  have h1 := Real.hasFDerivAt_fourier hint hint' w
  rw [hF] at h1
  have huniq : 𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) w = Fd := h1.unique hFd

  have hI : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) f) := by
    refine (hint'.const_mul (2 * π * ‖innerSL (E := E) ℝ‖)).mono' hint.aestronglyMeasurable.fourierSMulRight
      (Filter.Eventually.of_forall fun v => ?_)
    calc ‖VectorFourier.fourierSMulRight (innerSL ℝ) f v‖ ≤ 2 * π * ‖innerSL (E := E) ℝ‖ * ‖v‖ * ‖f v‖ :=
          VectorFourier.norm_fourierSMulRight_le _ _ _
      _ = 2 * π * ‖innerSL (E := E) ℝ‖ * (‖v‖ * ‖f v‖) := by ring
  have happly : (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) w) a
      = 𝓕 (fun v : E => VectorFourier.fourierSMulRight (innerSL ℝ) f v a) w :=
    Real.fourierIntegral_continuousLinearMap_apply' (L := innerSL ℝ) hI
  have hpt : (fun v : E => VectorFourier.fourierSMulRight (innerSL ℝ) f v a)
      = fun v => (-(2 * π * Complex.I)) * (((⟪a, v⟫_ℝ : ℝ) : ℂ) * f v) := by
    funext v
    rw [VectorFourier.fourierSMulRight_apply]
    change -(2 * (π : ℂ) * Complex.I) • (⟪v, a⟫_ℝ) • f v = _
    rw [real_inner_comm a v, Complex.real_smul, smul_eq_mul]
  have hlin : 𝓕 (fun v : E => (-(2 * π * Complex.I)) * (((⟪a, v⟫_ℝ : ℝ) : ℂ) * f v)) w
      = (-(2 * π * Complex.I)) * 𝓕 (fun v : E => ((⟪a, v⟫_ℝ : ℝ) : ℂ) * f v) w := by
    rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => by
      simp only [Circle.smul_def, smul_eq_mul]; ring)
  have hc : (-(2 * π * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : (-(2 * π * Complex.I)) * 𝓕 (fun v : E => ((⟪a, v⟫_ℝ : ℝ) : ℂ) * f v) w = Fd a := by
    rw [← hlin, ← hpt, ← happly, huniq]
  rw [← key, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

private theorem hasFDerivAt_innerC (a w : E) :
    HasFDerivAt (fun x : E => ((⟪a, x⟫_ℝ : ℝ) : ℂ)) (Complex.ofRealCLM.comp (innerSL ℝ a)) w :=
  Complex.ofRealCLM.hasFDerivAt.comp w (innerSL ℝ a).hasFDerivAt

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

private theorem hasFDerivAt_polyS [DecidableEq σ] (S : Finset σ) (w : E) :
    HasFDerivAt (polyS e S)
      (∑ i ∈ S, (∏ j ∈ S.erase i, ((⟪e j, w⟫_ℝ : ℝ) : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ (e i)))) w := by
  have h := HasFDerivAt.finsetProd (u := S) (g := fun i (x : E) => ((⟪e i, x⟫_ℝ : ℝ) : ℂ))
    (g' := fun i => Complex.ofRealCLM.comp (innerSL ℝ (e i))) (x := w) fun i _ => hasFDerivAt_innerC (e i) w
  convert h using 1 <;> rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem polyS_fderiv_apply_eq_zero [DecidableEq σ] (he : Orthonormal ℝ e) (S : Finset σ) (w : E)
    {u : σ} (hu : u ∉ S) :
    (∑ i ∈ S, (∏ j ∈ S.erase i, ((⟪e j, w⟫_ℝ : ℝ) : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ (e i)))) (e u) = 0 := by
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hne : i ≠ u := fun h => hu (h ▸ hi)
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    Complex.ofRealCLM_apply, orthonormal_iff_ite.mp he i u, if_neg hne]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

private theorem hasFDerivAt_gaussFT (t : ℝ) (w : E) :
    HasFDerivAt (gaussFT (E := E) t)
      ((gaussFT t w * (-(π : ℂ) / t)) • (Complex.ofRealCLM.comp ((2 : ℝ) • innerSL ℝ w))) w := by
  have hq0 : HasFDerivAt (fun x : E => ‖x‖ ^ 2) ((2 : ℝ) • innerSL ℝ w) w := by
    convert (hasStrictFDerivAt_norm_sq w).hasFDerivAt using 1
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  have hq : HasFDerivAt (fun x : E => ((‖x‖ ^ 2 : ℝ) : ℂ)) (Complex.ofRealCLM.comp ((2 : ℝ) • innerSL ℝ w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hq0
  have hq' : HasFDerivAt (fun x : E => -(π : ℂ) / t * ((‖x‖ ^ 2 : ℝ) : ℂ))
      ((-(π : ℂ) / t) • Complex.ofRealCLM.comp ((2 : ℝ) • innerSL ℝ w)) w := hq.const_mul _
  have hexp := hq'.cexp
  have hfun : gaussFT (E := E) t = fun x => (1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)
      * Complex.exp (-(π : ℂ) / t * ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    funext x; simp [gaussFT]
  rw [hfun]
  convert hexp.const_mul ((1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)) using 1 <;> try rfl
  simp only [smul_smul, smul_eq_mul]
  congr 1
  push_cast
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

private theorem hasFDerivAt_explicit [DecidableEq σ] (t : ℝ) (S : Finset σ) (C : ℂ) (w : E) :
    HasFDerivAt (fun x : E => C * polyS e S x * gaussFT t x)
      (C • ((polyS e S w) • ((gaussFT t w * (-(π : ℂ) / t)) • (Complex.ofRealCLM.comp ((2 : ℝ) • innerSL ℝ w)))
        + (gaussFT t w) • (∑ i ∈ S, (∏ j ∈ S.erase i, ((⟪e j, w⟫_ℝ : ℝ) : ℂ))
            • (Complex.ofRealCLM.comp (innerSL ℝ (e i)))))) w := by
  have hPG := ((hasFDerivAt_polyS e S w).mul (hasFDerivAt_gaussFT (E := E) t w)).const_mul C
  have hfun : (fun x : E => C * polyS e S x * gaussFT t x) = fun y => C * ((polyS e S * gaussFT t : E → ℂ) y) := by
    funext y; simp only [Pi.mul_apply]; ring
  rw [hfun]
  exact hPG

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

private theorem explicit_fderiv_apply [DecidableEq σ] (he : Orthonormal ℝ e) (t : ℝ) (S : Finset σ) (C : ℂ) (w : E)
    {u : σ} (hu : u ∉ S) :
    (C • ((polyS e S w) • ((gaussFT t w * (-(π : ℂ) / t)) • (Complex.ofRealCLM.comp ((2 : ℝ) • innerSL ℝ w)))
        + (gaussFT t w) • (∑ i ∈ S, (∏ j ∈ S.erase i, ((⟪e j, w⟫_ℝ : ℝ) : ℂ))
            • (Complex.ofRealCLM.comp (innerSL ℝ (e i)))))) (e u)
      = C * polyS e S w * gaussFT t w * (-(π : ℂ) / t) * (2 * ((⟪w, e u⟫_ℝ : ℝ) : ℂ)) := by
  have h0 := polyS_fderiv_apply_eq_zero e he S w hu
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, h0,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem polyS_insert [DecidableEq σ] {u : σ} {S : Finset σ} (hu : u ∉ S) (x : E) :
    polyS e (insert u S) x = ((⟪e u, x⟫_ℝ : ℝ) : ℂ) * polyS e S x := by
  simp [polyS, Finset.prod_insert hu]

private theorem fourier_oddGaussian [DecidableEq σ] (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ) :
    𝓕 (oddGaussian e t S) = fun w => (-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card * polyS e S w * gaussFT t w := by
  induction S using Finset.induction_on with
  | empty =>
    funext w
    have : oddGaussian e t ∅ = ⇑(gaussianMap (E := E) t) := by
      funext x; simp [oddGaussian, polyS]
    rw [this, fourier_gaussianMap ht w]
    simp [polyS, gaussFT]
  | insert u S hu ih =>
    funext w
    have hFd := hasFDerivAt_explicit e t S ((-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card) w
    have hF : 𝓕 (oddGaussian e t S) = fun x : E => (-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card * polyS e S x * gaussFT t x :=
      ih
    have hstep := fourier_inner_mul_of_hasFDerivAt (integrable_oddGaussian e he ht S)
      (integrable_norm_mul_oddGaussian e he ht S) hF hFd (e u)
    have hins : oddGaussian e t (insert u S) = fun v : E => ((⟪e u, v⟫_ℝ : ℝ) : ℂ) * oddGaussian e t S v := by
      funext v
      simp only [oddGaussian, polyS_insert e hu]
      ring
    rw [hins, hstep, explicit_fderiv_apply e he t S _ w hu, Finset.card_insert_of_notMem hu, real_inner_comm,
      polyS_insert e hu, pow_succ, pow_succ]
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hc : (-(2 * (π : ℂ) * Complex.I)) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have key : (-(2 * (π : ℂ) * Complex.I))⁻¹ * (-(π : ℂ) / t * 2) = -Complex.I * (1 / t) := by
      rw [inv_mul_eq_iff_eq_mul₀ hc,
        show -(2 * (π : ℂ) * Complex.I) * (-Complex.I * (1 / t)) = 2 * π * (Complex.I * Complex.I) / t by ring,
        Complex.I_mul_I]
      ring
    linear_combination ((-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card * polyS e S w * gaussFT t w
      * (((⟪e u, w⟫_ℝ : ℝ) : ℂ))) * key

section Poisson

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private theorem norm_oddGaussian_le_half (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ) (x : E) :
    ‖oddGaussian e t S x‖ ≤ oddConst t S.card * ‖gaussianMap (t / 2) x‖ := by
  rw [norm_gaussianMap]
  exact (norm_oddGaussian_le e he t S x).trans (norm_pow_mul_gaussian_le ht S.card x)

private def oddTranslatedMap (t : ℝ) (S : Finset σ) (v₀ : E) : C(E, ℂ) :=
  ⟨fun x => oddGaussian e t S (x + v₀), (continuous_oddGaussian e t S).comp (continuous_id.add continuous_const)⟩

private theorem oddTranslated_translateNorm_summable (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ)
    (v₀ : E) (K : TopologicalSpace.Compacts E) :
    Summable fun v : L =>
      ‖((oddTranslatedMap e t S v₀).comp (ContinuousMap.addRight (v : E))).restrict (K : Set E)‖ := by
  have hC := (oddConst_pos ht S.card).le
  have hbig := (translatedGaussian_translateNorm_summable L (half_pos ht) v₀ K).mul_left (oddConst t S.card)
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hbig
  rw [ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))]
  rintro ⟨x, hx⟩
  calc ‖((oddTranslatedMap e t S v₀).comp (ContinuousMap.addRight (v : E))).restrict (K : Set E) ⟨x, hx⟩‖
      = ‖oddGaussian e t S (x + (v : E) + v₀)‖ := rfl
    _ ≤ oddConst t S.card * ‖gaussianMap (t / 2) (x + (v : E) + v₀)‖ := norm_oddGaussian_le_half e he ht S _
    _ = oddConst t S.card
          * ‖((translatedGaussianMap (t / 2) v₀).comp (ContinuousMap.addRight (v : E))).restrict (K : Set E) ⟨x, hx⟩‖ :=
        rfl
    _ ≤ oddConst t S.card
          * ‖((translatedGaussianMap (t / 2) v₀).comp (ContinuousMap.addRight (v : E))).restrict (K : Set E)‖ :=
        mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) hC

private theorem fourier_oddTranslatedMap [DecidableEq σ] (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ)
    (v₀ w : E) :
    𝓕 ⇑(oddTranslatedMap e t S v₀) w
      = 𝐞 ⟪v₀, w⟫_ℝ • ((-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card * polyS e S w * gaussFT t w) := by
  have hcoe : ⇑(oddTranslatedMap e t S v₀) = (oddGaussian e t S) ∘ (fun x => x + v₀) := rfl
  have hlaw := VectorFourier.fourierIntegral_comp_add_right 𝐞 (volume : Measure E) (innerₗ E)
    (oddGaussian e t S) v₀
  rw [hcoe]
  show VectorFourier.fourierIntegral 𝐞 volume (innerₗ E) ((oddGaussian e t S) ∘ (fun x => x + v₀)) w = _
  simp only [hlaw]
  rw [show VectorFourier.fourierIntegral 𝐞 volume (innerₗ E) (oddGaussian e t S) w = 𝓕 (oddGaussian e t S) w from rfl,
    fourier_oddGaussian e he ht S]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

private theorem norm_explicit_le (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ) (w : E) :
    ‖(-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card * polyS e S w * gaussFT t w‖
      ≤ (1 / t) ^ S.card * ‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖ * oddConst (1 / t) S.card
          * Real.exp (-π * (1 / t / 2) * ‖w‖ ^ 2) := by
  have hti : (0 : ℝ) < 1 / t := by positivity
  have hI : ‖(-Complex.I) ^ S.card‖ = 1 := by rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hT : ‖(1 / (t : ℂ)) ^ S.card‖ = (1 / t) ^ S.card := by
    rw [norm_pow]; congr 1
    rw [show (1 / (t : ℂ)) = ((1 / t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg hti.le]
  have hG : ‖gaussFT (E := E) t w‖
      = ‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖ * Real.exp (-π * (1 / t) * ‖w‖ ^ 2) := by
    rw [gaussFT, norm_mul]
    congr 1
    rw [show -(π : ℂ) / t * (‖w‖ : ℂ) ^ 2 = ((-π * (1 / t) * ‖w‖ ^ 2 : ℝ) : ℂ) from by push_cast; ring,
      ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  rw [norm_mul, norm_mul, norm_mul, hI, one_mul, hT, hG]
  have hP := norm_polyS_le e he S w
  have hdom := norm_pow_mul_gaussian_le (E := E) hti S.card w
  have h0 : 0 ≤ ‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖ := norm_nonneg _
  calc (1 / t) ^ S.card * ‖polyS e S w‖ * (‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖ * Real.exp (-π * (1 / t) * ‖w‖ ^ 2))
      = (1 / t) ^ S.card * ‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖
          * (‖polyS e S w‖ * Real.exp (-π * (1 / t) * ‖w‖ ^ 2)) := by ring
    _ ≤ (1 / t) ^ S.card * ‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖
          * (‖w‖ ^ S.card * Real.exp (-π * (1 / t) * ‖w‖ ^ 2)) := by gcongr
    _ ≤ (1 / t) ^ S.card * ‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖
          * (oddConst (1 / t) S.card * Real.exp (-π * (1 / t / 2) * ‖w‖ ^ 2)) := by gcongr
    _ = _ := by ring

private theorem oddTranslated_fourier_summable [DecidableEq σ] (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t)
    (S : Finset σ) (v₀ : E) :
    Summable fun w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L =>
      𝓕 ⇑(oddTranslatedMap e t S v₀) (w : E) := by
  have hti2 : (0 : ℝ) < 1 / t / 2 := by positivity
  have hs := Deep.Analytic.latticeThetaSummable (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) hti2
  rw [Deep.Analytic.LatticeThetaSummable] at hs
  refine Summable.of_norm_bounded (hs.mul_left
    ((1 / t) ^ S.card * ‖(1 / (t : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2)‖ * oddConst (1 / t) S.card)) fun w => ?_
  rw [fourier_oddTranslatedMap e he ht S v₀ (w : E), Circle.norm_smul]
  exact norm_explicit_le e he ht S (w : E)

private theorem phase_oddGaussian_summable [DecidableEq σ] (he : Orthonormal ℝ e) (r : E) {t : ℝ} (ht : 0 < t)
    (S : Finset σ) :
    Summable fun m : LinearMap.BilinForm.dualSubmodule (innerₗ E) L =>
      (𝐞 ⟪r, (m : E)⟫_ℝ : ℂ) * (polyS e S (m : E) * gaussFT t (m : E)) := by
  set C : ℂ := (-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card with hCdef
  have hC : C ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) (pow_ne_zero _ ?_)
    rw [one_div]; exact inv_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  have hs := (oddTranslated_fourier_summable e L he ht S r).mul_left C⁻¹
  refine hs.congr fun m => ?_
  rw [fourier_oddTranslatedMap e he ht S r (m : E), Circle.smul_def, smul_eq_mul, ← hCdef]
  field_simp

private theorem oddTranslatedTheta_poisson [DecidableEq σ] (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t) (S : Finset σ)
    (v₀ : E) :
    ∑' v : L, oddGaussian e t S ((v : E) + v₀)
      = (ZLattice.covolume L volume : ℂ)⁻¹ * ((-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card)
          * ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
              (𝐞 ⟪v₀, (w : E)⟫_ℝ : ℂ) * (polyS e S (w : E) * gaussFT t (w : E)) := by
  have h := tsum_lattice_eq_covolume_inv_mul_tsum_fourier (E := E) L (oddTranslatedMap e t S v₀)
    (fun K => oddTranslated_translateNorm_summable e L he ht S v₀ K) (oddTranslated_fourier_summable e L he ht S v₀)
  have hL : ∑' v : L, oddGaussian e t S ((v : E) + v₀) = ∑' v : L, oddTranslatedMap e t S v₀ (v : E) :=
    tsum_congr fun v => rfl
  rw [hL, h, mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  exact tsum_congr fun w => by
    rw [fourier_oddTranslatedMap e he ht S v₀ (w : E), Circle.smul_def, smul_eq_mul]
    ring

private theorem weightedOddCoset_poisson [DecidableEq σ] {ι : Type} [Fintype ι] (he : Orthonormal ℝ e)
    (rep : ι → E) (wt : ι → ℂ) {t : ℝ} (ht : 0 < t) (S : Finset σ) :
    ∑ i, wt i * ∑' v : L, oddGaussian e t S ((v : E) + rep i)
      = (ZLattice.covolume L volume : ℂ)⁻¹ * ((-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card)
          * ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
              (∑ i, wt i * (𝐞 ⟪rep i, (m : E)⟫_ℝ : ℂ)) * (polyS e S (m : E) * gaussFT t (m : E)) := by
  set C : ℂ := (ZLattice.covolume L volume : ℂ)⁻¹ * ((-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card) with hCdef
  have hstep : ∀ i : ι, wt i * ∑' v : L, oddGaussian e t S ((v : E) + rep i)
      = ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          C * (wt i * ((𝐞 ⟪rep i, (m : E)⟫_ℝ : ℂ) * (polyS e S (m : E) * gaussFT t (m : E)))) := by
    intro i
    rw [oddTranslatedTheta_poisson e L he ht S (rep i), ← hCdef, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun m => by ring
  calc ∑ i, wt i * ∑' v : L, oddGaussian e t S ((v : E) + rep i)
      = ∑ i, ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          C * (wt i * ((𝐞 ⟪rep i, (m : E)⟫_ℝ : ℂ) * (polyS e S (m : E) * gaussFT t (m : E)))) :=
        Finset.sum_congr rfl fun i _ => hstep i
    _ = ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          ∑ i, C * (wt i * ((𝐞 ⟪rep i, (m : E)⟫_ℝ : ℂ) * (polyS e S (m : E) * gaussFT t (m : E)))) := by
        refine (Summable.tsum_finsetSum fun i _ => ?_).symm
        exact ((phase_oddGaussian_summable e L he (rep i) ht S).mul_left (wt i)).mul_left C
    _ = ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          C * ((∑ i, wt i * (𝐞 ⟪rep i, (m : E)⟫_ℝ : ℂ)) * (polyS e S (m : E) * gaussFT t (m : E))) := by
        refine tsum_congr fun m => ?_
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [tsum_mul_left]

end Poisson
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

end TcFold_M4aTheta_OddCoset
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"

section TcFold_M4aTheta_RayBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private def uWeight (x : K) : ℂ :=
  chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x
      * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
    * signAt K S x

private def IsCoprimeGenerator (x₀ : K) : Prop :=
  x₀ ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ∧
    chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
      * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0

private theorem IsCoprimeGenerator.exists_scaled_unit (h𝔣 : 𝔣 ≠ ⊥) {x₀ : K}
    (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀) :
    ∃ (g : K) (a : 𝓞 K),
      g ∈ ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
        ∧ (a : K) = x₀ * g ∧ a - 1 ∈ 𝔣 := by
  obtain ⟨hmem, hne⟩ := hx₀
  by_cases h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
      * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0
  · rw [h0, chiIdeal_zero χ] at hne
    exact absurd rfl hne
  by_cases hc : Units.mk0 _ h0 ∈ coprimeToModulus K 𝔣
  swap
  · exact absurd (chiIdeal_eq_zero_of_not_mem χ h0 hc) hne
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
      * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
        ≤ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
            * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
          mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem) _
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨a, haI, ha1⟩ := exists_mem_sub_one_mem_of_coprime h𝔣 hle h0 hc
  obtain ⟨g, hg, hag⟩ := FractionalIdeal.mem_singleton_mul.mp haI
  exact ⟨g, a, hg, hag, ha1⟩

private theorem coset_cover (h𝔣 : 𝔣 ≠ ⊥) {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀)
    {x : K} (hx : x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ α : 𝓞 K, x - x₀ * (α : K)
      ∈ ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := by
  obtain ⟨g, a, hg, hag, ha1⟩ := hx₀.exists_scaled_unit K 𝔣 χ 𝔞 h𝔣
  have hgx : g * x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := FractionalIdeal.mul_mem_mul hg hx
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one] at h
  rw [FractionalIdeal.mem_one_iff] at hgx
  obtain ⟨α, hα⟩ := hgx
  refine ⟨α, ?_⟩
  have hxa : x - x₀ * (α : K) = x * (1 - (a : K)) := by
    have hαK : (α : K) = g * x := hα
    rw [hαK, hag]; ring
  rw [hxa]
  have h1a : (1 : 𝓞 K) - a ∈ 𝔣 := by
    have h := 𝔣.neg_mem ha1
    rwa [neg_sub] at h
  have h1aK : (1 : K) - (a : K) ∈ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨1 - a, h1a, by push_cast; ring⟩
  have h := FractionalIdeal.mul_mem_mul hx h1aK
  rwa [mul_comm ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)] at h

private theorem coset_inj (h𝔣 : 𝔣 ≠ ⊥) {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀) (α β : 𝓞 K) :
    (x₀ * (α : K) - x₀ * (β : K)
        ∈ ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)))
      ↔ α - β ∈ 𝔣 := by
  obtain ⟨g, a, hg, hag, ha1⟩ := hx₀.exists_scaled_unit K 𝔣 χ 𝔞 h𝔣
  constructor
  · intro hm
    have hK : ((α - β : 𝓞 K) : K) * (a : K)
        ∈ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      have h1 := FractionalIdeal.mul_mem_mul hm hg
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at h1
      have heq : ((α - β : 𝓞 K) : K) * (a : K) = (x₀ * (α : K) - x₀ * (β : K)) * g := by
        rw [hag]; push_cast; ring
      rwa [heq]
    rw [FractionalIdeal.mem_coeIdeal] at hK
    obtain ⟨c, hc𝔣, hcK⟩ := hK
    have hca : c = (α - β) * a := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [hcK, map_mul]
    have hstep : α - β = (α - β) * a - (α - β) * (a - 1) := by ring
    rw [hstep]
    exact sub_mem (hca ▸ hc𝔣) (Ideal.mul_mem_left _ _ ha1)
  · intro hd
    have hdK : (α : K) - (β : K) ∈ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨α - β, hd, by push_cast; ring⟩
    have h := FractionalIdeal.mul_mem_mul hdK hx₀.1
    have hshape : x₀ * (α : K) - x₀ * (β : K) = ((α : K) - (β : K)) * x₀ := by ring
    rwa [hshape]

private theorem IsCoprimeGenerator.spanFI_coprime {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀) :
    ∃ h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0,
      Units.mk0 _ h0 ∈ coprimeToModulus K 𝔣 := by
  obtain ⟨-, hne⟩ := hx₀
  by_cases h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
      * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0
  · rw [h0, chiIdeal_zero χ] at hne
    exact absurd rfl hne
  by_cases hc : Units.mk0 _ h0 ∈ coprimeToModulus K 𝔣
  · exact ⟨h0, hc⟩
  · exact absurd (chiIdeal_eq_zero_of_not_mem χ h0 hc) hne

private theorem chiIdeal_mul_coprime_right {X C : FractionalIdeal (𝓞 K)⁰ K} (hX : X ≠ 0) (hC : C ≠ 0)
    (hCc : Units.mk0 C hC ∈ coprimeToModulus K 𝔣) :
    chiIdeal K 𝔣 χ (X * C) = chiIdeal K 𝔣 χ X * chiIdeal K 𝔣 χ C := by
  by_cases hXc : Units.mk0 X hX ∈ coprimeToModulus K 𝔣
  · exact chiIdeal_mul_of_mem χ hX hC hXc hCc
  · have hXC : X * C ≠ 0 := mul_ne_zero hX hC
    have hXCc : Units.mk0 (X * C) hXC ∉ coprimeToModulus K 𝔣 := by
      intro hmem
      apply hXc
      have hmk : Units.mk0 (X * C) hXC = Units.mk0 X hX * Units.mk0 C hC := Units.ext rfl
      rw [hmk] at hmem
      exact (mul_mem_cancel_right hCc).mp hmem
    rw [chiIdeal_eq_zero_of_not_mem χ hXC hXCc, chiIdeal_eq_zero_of_not_mem χ hX hXc, zero_mul]

private theorem chiIdeal_eq_zero_of_le_coe (h𝔣' : 𝔣 ≠ ⊤) {J : FractionalIdeal (𝓞 K)⁰ K}
    (hJ0 : J ≠ 0) (hle : J ≤ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    chiIdeal K 𝔣 χ J = 0 := by
  by_cases hc : Units.mk0 J hJ0 ∈ coprimeToModulus K 𝔣
  swap
  · exact chiIdeal_eq_zero_of_not_mem χ hJ0 hc
  exfalso
  have h𝔣0 : 𝔣 ≠ ⊥ := by
    rintro rfl
    apply hJ0
    rw [le_antisymm_iff]
    constructor
    · simpa using hle
    · exact FractionalIdeal.zero_le _
  have hle1 : J ≤ 1 := le_trans hle (by
    rw [← FractionalIdeal.coeIdeal_top]
    exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr le_top)
  obtain ⟨J₀, hJ₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
  have hJ₀0 : J₀ ≠ ⊥ := by
    rintro rfl
    exact hJ0 (by rw [← hJ₀, FractionalIdeal.coeIdeal_bot])
  have hJ₀le : J₀ ≤ 𝔣 := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K, hJ₀]
    exact hle
  obtain ⟨mx, hmx, hlemx⟩ := Ideal.exists_le_maximal 𝔣 h𝔣'
  have hmbot : mx ≠ ⊥ := fun h => h𝔣0 (le_bot_iff.mp (h ▸ hlemx))
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨mx, hmx.isPrime, hmbot⟩
  have hvdvd : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.mpr hlemx
  have hvJ : v.asIdeal ∣ J₀ := Ideal.dvd_iff_le.mpr (le_trans hJ₀le hlemx)
  have hcnt := (mem_coprimeToModulus_iff K).mp hc v hvdvd
  rw [Units.val_mk0, ← hJ₀, FractionalIdeal.count_coe K v (show J₀ ≠ 0 from hJ₀0)] at hcnt
  have hz : (Associates.mk v.asIdeal).count (Associates.mk J₀).factors = 0 := by exact_mod_cast hcnt
  exact ((Associates.count_ne_zero_iff_dvd (show J₀ ≠ 0 from hJ₀0) v.irreducible).mpr hvJ) hz

private theorem uWeight_add_mem (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) (hP : IsParity K 𝔣 χ S)
    {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀) (α : 𝓞 K) {m : K}
    (hm : m ∈ ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K))) :
    uWeight K 𝔣 χ S 𝔞 (x₀ * (α : K) + m) = chiFin K 𝔣 χ S α * uWeight K 𝔣 χ S 𝔞 x₀ := by
  obtain ⟨g, a, hg, hag, ha1⟩ := hx₀.exists_scaled_unit K 𝔣 χ 𝔞 h𝔣
  obtain ⟨hI₀0, hI₀c⟩ := hx₀.spanFI_coprime K 𝔣 χ 𝔞
  have hx₀mem := hx₀.1
  have hx₀ne : x₀ ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero, zero_mul] at hI₀0
    exact hI₀0 rfl
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply h𝔣'
    rw [Ideal.eq_top_iff_one]
    have h := 𝔣.neg_mem ha1
    rwa [neg_sub, sub_zero] at h
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hag
    exact ha0 (by exact_mod_cast hag)
  have hbridge : ∀ β : 𝓞 K, ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K) := fun β => by
    rw [FractionalIdeal.coeIdeal_span_singleton]

  have hmgmem : m * g ∈ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := FractionalIdeal.mul_mem_mul hm hg
    rwa [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at h
  rw [FractionalIdeal.mem_coeIdeal] at hmgmem
  obtain ⟨μ, hμ𝔣, hμK'⟩ := hmgmem
  have hμK : (μ : K) = m * g := hμK'
  have hagK : (a : K) = x₀ * g := hag

  by_cases hα0 : α = 0
  · subst hα0
    have harg : x₀ * ((0 : 𝓞 K) : K) + m = m := by push_cast; ring
    rw [uWeight, harg, chiFin, show ((Ideal.span {(0 : 𝓞 K)} : Ideal (𝓞 K))
        : FractionalIdeal (𝓞 K)⁰ K) = 0 by
      rw [Ideal.span_singleton_eq_bot.mpr rfl]
      exact FractionalIdeal.coeIdeal_bot, chiIdeal_zero, zero_mul, zero_mul]
    by_cases hm0 : m = 0
    · rw [hm0, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero, zero_mul]
    · have hJ0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ m
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
        mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hm0) (Units.ne_zero 𝔞⁻¹)
      have hJle : FractionalIdeal.spanSingleton (𝓞 K)⁰ m
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
            ≤ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ m
            ≤ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
          FractionalIdeal.spanSingleton_le_iff_mem.mpr hm
        calc FractionalIdeal.spanSingleton (𝓞 K)⁰ m
            * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
            ≤ (((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
                * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
              mul_le_mul_left h1 _
          _ = ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
              rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rw [chiIdeal_eq_zero_of_le_coe K 𝔣 χ h𝔣' hJ0 hJle, zero_mul]

  set X : K := x₀ * (α : K) + m with hXdef
  by_cases hX0 : X = 0
  · have hαin : α ∈ 𝔣 := by
      have hmem𝔣𝔞 : x₀ * (α : K) - x₀ * ((0 : 𝓞 K) : K)
          ∈ ((𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
        have hxm : x₀ * (α : K) = -m := by
          have h := hX0
          rw [hXdef] at h
          linear_combination h
        rw [show x₀ * (α : K) - x₀ * ((0 : 𝓞 K) : K) = x₀ * (α : K) by push_cast; ring, hxm]
        rw [← FractionalIdeal.mem_coe] at hm ⊢
        exact neg_mem hm
      have h := (coset_inj K 𝔣 χ 𝔞 h𝔣 hx₀ α 0).mp hmem𝔣𝔞
      simpa using h
    have hspanle : (Ideal.span {α} : Ideal (𝓞 K)) ≤ 𝔣 := by
      rw [Ideal.span_le]
      simpa using hαin
    rw [uWeight, hX0, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero,
      zero_mul, chiFin]
    rcases eq_or_ne ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) 0 with hz | hz
    · rw [hz, chiIdeal_zero, zero_mul, zero_mul]
    · rw [chiIdeal_eq_zero_of_le_coe K 𝔣 χ h𝔣' hz
        ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hspanle), zero_mul, zero_mul]

  have hXspan0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ X ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hX0
  have hA₀K : ((a * α + μ : 𝓞 K) : K) = X * g := by
    push_cast [hμK, hagK, hXdef]
    ring
  have hA₀Kne : ((a * α + μ : 𝓞 K) : K) ≠ 0 := by
    rw [hA₀K]; exact mul_ne_zero hX0 hg0
  have hαKne : (α : K) ≠ 0 := by exact_mod_cast hα0

  have haspan0 : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hbridge]
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr (by exact_mod_cast ha0)
  have haspanc : Units.mk0 _ haspan0 ∈ coprimeToModulus K 𝔣 := by
    have hmk : Units.mk0 _ haspan0 = principalUnit K a ha0 := by
      apply Units.ext
      rw [Units.val_mk0, principalUnit_val]
    rw [hmk]
    exact principalUnit_mem_coprimeToModulus K ha0 ha1
  have hχa : chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    chiIdeal_ne_zero_of_mem χ haspan0 haspanc

  have hJ0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ X
      * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    mul_ne_zero hXspan0 (Units.ne_zero 𝔞⁻¹)
  have hA₀span0 : ((Ideal.span {a * α + μ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hbridge]
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hA₀Kne
  have heq1 : ((Ideal.span {a * α + μ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
      = (FractionalIdeal.spanSingleton (𝓞 K)⁰ X
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
        * ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hbridge, hbridge, hA₀K, hagK, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    ring
  have hM1 : chiIdeal K 𝔣 χ ((Ideal.span {a * α + μ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        * chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
      = chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ X
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
        * chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← chiIdeal_mul_coprime_right K 𝔣 χ hA₀span0 hI₀0 hI₀c,
      ← chiIdeal_mul_coprime_right K 𝔣 χ hJ0 haspan0 haspanc, heq1]
  have hαspan0 : ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hbridge]
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hαKne
  have hM2 : chiIdeal K 𝔣 χ ((Ideal.span {a * α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        * chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [show (Ideal.span {a * α} : Ideal (𝓞 K)) = Ideal.span {α} * Ideal.span {a} by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm],
      FractionalIdeal.coeIdeal_mul, chiIdeal_mul_coprime_right K 𝔣 χ hαspan0 haspan0 haspanc]

  have hIII : chiIdeal K 𝔣 χ ((Ideal.span {a * α + μ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        * signAt K S ((a * α + μ : 𝓞 K) : K)
      = chiIdeal K 𝔣 χ ((Ideal.span {a * α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        * signAt K S ((a * α : 𝓞 K) : K) :=
    chiFin_congr_v2 K 𝔣 χ S hP h𝔣' (show (a * α + μ : 𝓞 K) - a * α ∈ 𝔣 by simpa using hμ𝔣)

  have hsgnA : signAt K S ((a * α + μ : 𝓞 K) : K) = signAt K S X * signAt K S g := by
    rw [hA₀K, signAt_mul]
  have hsgna : signAt K S (a : K) = signAt K S x₀ * signAt K S g := by
    rw [hagK, signAt_mul]
  have hsgnaα : signAt K S ((a * α : 𝓞 K) : K) = signAt K S (a : K) * signAt K S (α : K) := by
    rw [show ((a * α : 𝓞 K) : K) = (a : K) * (α : K) by push_cast; ring, signAt_mul]
  have hsX2 : signAt K S X * signAt K S X = 1 := signAt_mul_self S hX0
  have hsg2 : signAt K S g * signAt K S g = 1 := signAt_mul_self S hg0
  have hsA2 : signAt K S ((a * α + μ : 𝓞 K) : K) * signAt K S ((a * α + μ : 𝓞 K) : K) = 1 :=
    signAt_mul_self S hA₀Kne
  have hsAne : signAt K S ((a * α + μ : 𝓞 K) : K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsA2
    exact one_ne_zero hsA2.symm

  have hkey : uWeight K 𝔣 χ S 𝔞 X
        * (chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          * signAt K S ((a * α + μ : 𝓞 K) : K))
      = (chiFin K 𝔣 χ S α * uWeight K 𝔣 χ S 𝔞 x₀)
        * (chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          * signAt K S ((a * α + μ : 𝓞 K) : K)) := by
    have hchiFinα : chiFin K 𝔣 χ S α
        = chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          * signAt K S (α : K) := rfl
    rw [uWeight, uWeight, hchiFinα]
    calc (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ X
            * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) * signAt K S X)
          * (chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * signAt K S ((a * α + μ : 𝓞 K) : K))
        = (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ X
            * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
            * chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
            * (signAt K S X * signAt K S ((a * α + μ : 𝓞 K) : K)) := by ring
      _ = (chiIdeal K 𝔣 χ ((Ideal.span {a * α + μ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)))
            * (signAt K S X * signAt K S ((a * α + μ : 𝓞 K) : K)) := by rw [hM1]
      _ = (chiIdeal K 𝔣 χ ((Ideal.span {a * α + μ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * signAt K S ((a * α + μ : 𝓞 K) : K))
            * chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
            * signAt K S X := by ring
      _ = (chiIdeal K 𝔣 χ ((Ideal.span {a * α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * signAt K S ((a * α : 𝓞 K) : K))
            * chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
            * signAt K S X := by rw [hIII]
      _ = (chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
            * (signAt K S (a : K) * signAt K S (α : K))
            * chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
            * signAt K S X := by rw [hM2, hsgnaα]
      _ = (chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
            * ((signAt K S x₀ * signAt K S g) * signAt K S (α : K))
            * chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
            * signAt K S X := by rw [hsgna]
      _ = (chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * signAt K S (α : K)
            * (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
              * signAt K S x₀))
            * (chiIdeal K 𝔣 χ ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
              * (signAt K S X * signAt K S g)) := by ring
      _ = _ := by rw [← hsgnA]
  exact mul_right_cancel₀ (mul_ne_zero hχa hsAne) hkey

private def rayModIdeal (h𝔣 : 𝔣 ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 ((𝔣 : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣) * 𝔞

private theorem coe_rayModIdeal (h𝔣 : 𝔣 ≠ ⊥) :
    ((rayModIdeal K 𝔣 𝔞 h𝔣 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := rfl

private def dilLattice (N : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (euclideanIdealLattice K N) (mixedDilCLE K).symm.toLinearMap

private scoped instance discreteTopology_dilLattice (N : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (dilLattice K N) :=
  inferInstanceAs (DiscreteTopology
    (ZLattice.comap ℝ (euclideanIdealLattice K N) (mixedDilCLE K).symm.toLinearMap))

private scoped instance isZLattice_dilLattice (N : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (dilLattice K N) :=
  inferInstanceAs (IsZLattice ℝ
    (ZLattice.comap ℝ (euclideanIdealLattice K N) (mixedDilCLE K).symm.toLinearMap))

private def dilRayLattice (h𝔣 : 𝔣 ≠ ⊥) : Submodule ℤ (euclidean.mixedSpace K) :=
  dilLattice K (rayModIdeal K 𝔣 𝔞 h𝔣)

private def dilEmbed (y : K) : euclidean.mixedSpace K :=
  mixedDil K ((euclidean.toMixed K).symm (mixedEmbedding K y))

private theorem dilEmbed_add (y z : K) : dilEmbed K (y + z) = dilEmbed K y + dilEmbed K z := by
  unfold dilEmbed
  rw [map_add, map_add, map_add]

private theorem dilEmbed_mem {N : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {y : K}
    (hy : y ∈ (N : FractionalIdeal (𝓞 K)⁰ K)) : dilEmbed K y ∈ dilLattice K N := by
  show dilEmbed K y
    ∈ ZLattice.comap ℝ (euclideanIdealLattice K N) (mixedDilCLE K).symm.toLinearMap
  rw [ZLattice.comap, Submodule.mem_comap]
  show (mixedDilCLE K).symm (dilEmbed K y) ∈ euclideanIdealLattice K N
  have hsim : (mixedDilCLE K).symm (dilEmbed K y)
      = (euclidean.toMixed K).symm (mixedEmbedding K y) := by
    simp [dilEmbed, mixedDilCLE]
  rw [hsim]
  exact (mem_euclideanIdealLattice K N _).mpr ⟨y, hy, rfl⟩

private def dilIdealEquiv (N : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ↥(N : FractionalIdeal (𝓞 K)⁰ K) ≃ dilLattice K N :=
  Equiv.ofBijective
    (fun y => ⟨dilEmbed K (y : K), dilEmbed_mem K y.2⟩)
    ⟨fun y y' h => by
        have h1 := congrArg Subtype.val h
        have h2 : (euclidean.toMixed K).symm (mixedEmbedding K (y : K))
            = (euclidean.toMixed K).symm (mixedEmbedding K (y' : K)) :=
          (mixedDil K).injective h1
        exact Subtype.ext (mixedEmbedding_injective K ((euclidean.toMixed K).symm.injective h2)),
     fun v => by
        have hv : (v : euclidean.mixedSpace K)
            ∈ ZLattice.comap ℝ (euclideanIdealLattice K N) (mixedDilCLE K).symm.toLinearMap :=
          v.2
        rw [ZLattice.comap, Submodule.mem_comap] at hv
        have hv' : (mixedDilCLE K).symm (v : euclidean.mixedSpace K)
            ∈ euclideanIdealLattice K N := hv
        obtain ⟨y, hy, hyv⟩ := (mem_euclideanIdealLattice K N _).mp hv'
        refine ⟨⟨y, hy⟩, ?_⟩
        apply Subtype.ext
        show dilEmbed K y = (v : euclidean.mixedSpace K)
        have h2 := congrArg (mixedDil K) hyv
        simpa [dilEmbed, mixedDilCLE] using h2⟩

private def bridgeRep (x₀ : K) (a : 𝓞 K ⧸ 𝔣) : euclidean.mixedSpace K :=
  mixedDil K ((euclidean.toMixed K).symm
    (mixedEmbedding K (x₀ * ((Quotient.out a : 𝓞 K) : K))))

private theorem bridgeRep_eq_dilEmbed (x₀ : K) (a : 𝓞 K ⧸ 𝔣) :
    bridgeRep K 𝔣 x₀ a = dilEmbed K (x₀ * ((Quotient.out a : 𝓞 K) : K)) := rfl

private def raySub : AddSubgroup ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) where
  carrier := {u | (u : K) ∈ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)}
  add_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq, ← FractionalIdeal.mem_coe] at ha hb ⊢
    exact add_mem ha hb
  zero_mem' := by
    rw [Set.mem_setOf_eq, ← FractionalIdeal.mem_coe]
    exact zero_mem _
  neg_mem' := fun {a} ha => by
    rw [Set.mem_setOf_eq, ← FractionalIdeal.mem_coe] at ha ⊢
    exact neg_mem ha

private theorem mem_raySub {u : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)} :
    u ∈ raySub K 𝔣 𝔞
      ↔ (u : K) ∈ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  Iff.rfl

private def genPoint {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀) (a : 𝓞 K ⧸ 𝔣) :
    ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  ⟨x₀ * ((Quotient.out a : 𝓞 K) : K), by
    rw [FractionalIdeal.mem_coe]
    have h := Submodule.smul_mem ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      (Quotient.out a) (by rw [FractionalIdeal.mem_coe]; exact hx₀.1)
    rw [← FractionalIdeal.mem_coe]
    have heq : (Quotient.out a : 𝓞 K) • x₀ = x₀ * ((Quotient.out a : 𝓞 K) : K) := by
      rw [Algebra.smul_def]; ring
    rwa [heq] at h⟩

private noncomputable def cosetIndexEquiv (h𝔣 : 𝔣 ≠ ⊥) {x₀ : K}
    (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀) :
    (𝓞 K ⧸ 𝔣) ≃ (↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ⧸ raySub K 𝔣 𝔞) :=
  Equiv.ofBijective (fun a => QuotientAddGroup.mk (genPoint K 𝔣 χ 𝔞 hx₀ a))
    ⟨fun a b hab => by
        rw [QuotientAddGroup.eq] at hab
        rw [mem_raySub] at hab
        have hK : x₀ * ((Quotient.out b : 𝓞 K) : K) - x₀ * ((Quotient.out a : 𝓞 K) : K)
            ∈ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
          have : ((-(genPoint K 𝔣 χ 𝔞 hx₀ a) + genPoint K 𝔣 χ 𝔞 hx₀ b : ) : K)
              = x₀ * ((Quotient.out b : 𝓞 K) : K) - x₀ * ((Quotient.out a : 𝓞 K) : K) := by
            push_cast [genPoint]
            ring
          rwa [this] at hab
        have hd := (coset_inj K 𝔣 χ 𝔞 h𝔣 hx₀ (Quotient.out b) (Quotient.out a)).mp hK
        have : (Ideal.Quotient.mk 𝔣) (Quotient.out b) = (Ideal.Quotient.mk 𝔣) (Quotient.out a) :=
          Ideal.Quotient.eq.mpr hd
        rw [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at this
        exact this.symm,
     fun c => by
        obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
        have hy : (y : K) ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
          rw [← FractionalIdeal.mem_coe]; exact y.2
        obtain ⟨α, hα⟩ := coset_cover K 𝔣 χ 𝔞 h𝔣 hx₀ hy
        refine ⟨Ideal.Quotient.mk 𝔣 α, ?_⟩
        rw [QuotientAddGroup.eq, mem_raySub]
        have houtα : (Quotient.out (Ideal.Quotient.mk 𝔣 α) : 𝓞 K) - α ∈ 𝔣 := by
          rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
        have hx₀out : x₀ * ((Quotient.out (Ideal.Quotient.mk 𝔣 α) : 𝓞 K) : K) - x₀ * (α : K)
            ∈ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
          (coset_inj K 𝔣 χ 𝔞 h𝔣 hx₀ _ _).mpr houtα
        have hsplit : ((-(genPoint K 𝔣 χ 𝔞 hx₀ (Ideal.Quotient.mk 𝔣 α)) + y : ) : K)
            = -((x₀ * ((Quotient.out (Ideal.Quotient.mk 𝔣 α) : 𝓞 K) : K) - x₀ * (α : K))
                + ((x₀ * (α : K)) - (y : K))) := by
          push_cast [genPoint]
          ring
        rw [hsplit, ← FractionalIdeal.mem_coe]
        refine neg_mem (add_mem ?_ ?_)
        · rw [FractionalIdeal.mem_coe]; exact hx₀out
        · have h := neg_mem (FractionalIdeal.mem_coe.mpr hα)
          rw [neg_sub] at h
          exact h⟩

private theorem dilEmbed_fst (y : K) (v : {w : InfinitePlace K // IsReal w}) :
    (dilEmbed K y).fst v = embedding_of_isReal v.2 y := by
  unfold dilEmbed
  rw [mixedDil_apply_fst, toMixed_symm_fst, mixedEmbedding_apply_isReal]

private theorem abs_fst_le_norm (x : euclidean.mixedSpace K) (v : {w : InfinitePlace K // IsReal w}) :
    |x.fst v| ≤ ‖x‖ := by
  have h2 : (x.fst v) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq_sum]
    have h1 : (x.fst v) ^ 2 ≤ ∑ u : {w : InfinitePlace K // IsReal w}, (x.fst u) ^ 2 :=
      Finset.single_le_sum (f := fun u => (x.fst u) ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ v)
    have h2' : (0 : ℝ) ≤ ∑ w : {w : InfinitePlace K // IsComplex w}, Complex.normSq (x.snd w) :=
      Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _
    linarith
  calc |x.fst v| = Real.sqrt ((x.fst v) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

private theorem norm_rayWeight_le_one (h𝔣 : 𝔣 ≠ ⊥) (x : K) : ‖rayWeight K 𝔣 χ 𝔞 x‖ ≤ 1 := by
  rw [rayWeight]
  split_ifs with hx htop
  · simp
  · simp
  · rcases eq_or_ne (FractionalIdeal.spanSingleton (𝓞 K)⁰ x
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) 0 with h0 | h0
    · rw [h0, chiIdeal_zero]
      simp
    · by_cases hc : Units.mk0 _ h0 ∈ coprimeToModulus K 𝔣
      · rw [norm_chiIdeal_of_mem χ h𝔣 h0 hc]
      · rw [chiIdeal_eq_zero_of_not_mem χ h0 hc]
        simp

private theorem raySummand_summable (h𝔣 : 𝔣 ≠ ⊥) {t : ℝ} (ht : 0 < t) :
    Summable fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      rayWeight K 𝔣 χ 𝔞 (x : K)
        * (((∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K))
            * Real.exp (-π * rayScale K 𝔣 𝔞 * t * heckeForm K (x : K)) : ℝ) : ℂ) := by
  have hc : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  have hct : 0 < rayScale K 𝔣 𝔞 * t := mul_pos hc ht
  set c := rayScale K 𝔣 𝔞 with hcdef
  set k := S.card with hkdef

  have hlat : Summable fun v : dilLattice K 𝔞 =>
      Real.exp (-π * (c * t / 2) * ‖(v : euclidean.mixedSpace K)‖ ^ 2) := by
    have h := latticeThetaSummable (E := euclidean.mixedSpace K) (dilLattice K 𝔞)
      (half_pos hct)
    rwa [LatticeThetaSummable] at h
  have hdom : Summable fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      Real.exp (-π * (c * t / 2) * ‖dilEmbed K (x : K)‖ ^ 2) := by
    have := (Equiv.summable_iff (dilIdealEquiv K 𝔞)).mpr hlat
    exact this
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _)
    (fun x => ?_) ((hdom.mul_left ((Real.sqrt c) ^ k * oddConst (c * t) k)))

  have hQ : heckeForm K (x : K) = ‖dilEmbed K (x : K)‖ ^ 2 := heckeForm_eq_norm_sq_mixedDil K _
  have hP0 : (0 : ℝ) ≤ ∏ v ∈ S, Real.sqrt c * v.1 (x : K) :=
    Finset.prod_nonneg fun v _ => mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hE0 : (0 : ℝ) < Real.exp (-π * c * t * heckeForm K (x : K)) := Real.exp_pos _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hP0 hE0.le)]
  have hb1 : ‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
        * ((∏ v ∈ S, Real.sqrt c * v.1 (x : K))
          * Real.exp (-π * c * t * heckeForm K (x : K)))
      ≤ (∏ v ∈ S, Real.sqrt c * v.1 (x : K))
          * Real.exp (-π * c * t * heckeForm K (x : K)) := by
    have := norm_rayWeight_le_one K 𝔣 χ 𝔞 h𝔣 (x : K)
    nlinarith [mul_nonneg hP0 hE0.le]
  refine hb1.trans ?_

  have hPle : (∏ v ∈ S, Real.sqrt c * v.1 (x : K))
      ≤ (Real.sqrt c * ‖dilEmbed K (x : K)‖) ^ k := by
    rw [hkdef, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun v _ => mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _))
      (fun v _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h1 : v.1 (x : K) = |(dilEmbed K (x : K)).fst v| := by
      rw [dilEmbed_fst, ← norm_embedding_of_isReal v.2, Real.norm_eq_abs]
    rw [h1]
    exact abs_fst_le_norm K _ v
  have hexp : Real.exp (-π * c * t * heckeForm K (x : K))
      = Real.exp (-π * (c * t) * ‖dilEmbed K (x : K)‖ ^ 2) := by
    rw [hQ]; ring_nf
  calc (∏ v ∈ S, Real.sqrt c * v.1 (x : K))
        * Real.exp (-π * c * t * heckeForm K (x : K))
      ≤ (Real.sqrt c * ‖dilEmbed K (x : K)‖) ^ k
        * Real.exp (-π * (c * t) * ‖dilEmbed K (x : K)‖ ^ 2) := by
        rw [← hexp]
        exact mul_le_mul_of_nonneg_right hPle hE0.le
    _ = (Real.sqrt c) ^ k
        * (‖dilEmbed K (x : K)‖ ^ k
          * Real.exp (-π * (c * t) * ‖dilEmbed K (x : K)‖ ^ 2)) := by
        rw [mul_pow]; ring
    _ ≤ (Real.sqrt c) ^ k
        * (oddConst (c * t) k
          * Real.exp (-π * (c * t / 2) * ‖dilEmbed K (x : K)‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg _) _)
        have h := norm_pow_mul_gaussian_le (E := euclidean.mixedSpace K) hct k
          (dilEmbed K (x : K))
        have harg : -π * (c * t) / 2 = -π * (c * t / 2) := by ring
        calc ‖dilEmbed K (x : K)‖ ^ k
              * Real.exp (-π * (c * t) * ‖dilEmbed K (x : K)‖ ^ 2)
            ≤ oddConst (c * t) k
              * Real.exp (-π * ((c * t) / 2) * ‖dilEmbed K (x : K)‖ ^ 2) := h
          _ = oddConst (c * t) k
              * Real.exp (-π * (c * t / 2) * ‖dilEmbed K (x : K)‖ ^ 2) := by norm_num
    _ = (Real.sqrt c) ^ k * oddConst (c * t) k
        * Real.exp (-π * (c * t / 2) * ‖dilEmbed K (x : K)‖ ^ 2) := by ring

private theorem coe_mul_le_self :
    (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      ≤ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  calc (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      ≤ 1 * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
        refine mul_le_mul_left ?_ _
        rw [← FractionalIdeal.coeIdeal_top]
        exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr le_top
    _ = (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := one_mul _

private noncomputable def raySubLatticeEquiv (h𝔣 : 𝔣 ≠ ⊥) :
    ↥(raySub K 𝔣 𝔞) ≃ ↥(dilRayLattice K 𝔣 𝔞 h𝔣) :=
  ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
    (Equiv.subtypeEquivRight fun y => by
      rw [coe_rayModIdeal]
      constructor
      · rintro ⟨h, hy⟩
        exact hy
      · intro hy
        exact ⟨FractionalIdeal.mem_coe.mpr (coe_mul_le_self K 𝔣 𝔞 hy), hy⟩)).trans
    ((dilIdealEquiv K (rayModIdeal K 𝔣 𝔞 h𝔣)).trans
      (Equiv.refl ↥(dilRayLattice K 𝔣 𝔞 h𝔣)))

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTheta_RayBridge
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_RayUnitWeight

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

p2m_open "NumberField NumberField.InfinitePlace Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem spanSingleton_coe_coe_unit (u : (𝓞 K)ˣ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) : K) = 1 := by
  rw [show ((u : 𝓞 K) : K) = algebraMap (𝓞 K) K (u : 𝓞 K) from rfl,
    ← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
    FractionalIdeal.coeIdeal_top]

private theorem uWeight_unit_smul (u : (𝓞 K)ˣ) (x : K) :
    uWeight K 𝔣 χ S 𝔞 (((u : 𝓞 K) : K) * x)
      = signAt K S ((u : 𝓞 K) : K) * uWeight K 𝔣 χ S 𝔞 x := by
  rw [uWeight, uWeight, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    spanSingleton_coe_coe_unit, one_mul, signAt_mul]
  ring

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_RayUnitWeight
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_TorusTheta

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

p2m_open "Real MeasureTheory Set Filter Function Topology Module Matrix NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

open scoped nonZeroDivisors RealInnerProductSpace Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

private def mulEquiv (a : ℝ) (ha : 0 < a) : ℝ ≃ₗ[ℝ] ℝ where
  toFun x := a * x
  invFun x := x / a
  map_add' x y := by ring
  map_smul' r x := by
    simp only [RingHom.id_apply, smul_eq_mul]
    ring
  left_inv x := by
    show a * x / a = x
    field_simp
  right_inv x := by
    show a * (x / a) = x
    field_simp

private def cmulEquiv (a : ℝ) (ha : 0 < a) : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := (a : ℂ) * z
  invFun z := z / (a : ℂ)
  map_add' z w := by ring
  map_smul' r z := by
    simp only [RingHom.id_apply, Complex.real_smul]
    ring
  left_inv z := by
    have h : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    show (a : ℂ) * z / (a : ℂ) = z
    field_simp
  right_inv z := by
    have h : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    show (a : ℂ) * (z / (a : ℂ)) = z
    field_simp

private def placeScale (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w) :
    (euclidean.mixedSpace K) ≃ₗ[ℝ] (euclidean.mixedSpace K) :=
  (WithLp.linearEquiv 2 ℝ _).trans <|
    ((((WithLp.linearEquiv 2 ℝ ({w : InfinitePlace K // IsReal w} → ℝ)).trans <|
        (LinearEquiv.piCongrRight fun v : {w : InfinitePlace K // IsReal w} =>
            mulEquiv (c v.1) (hc v.1)).trans
          (WithLp.linearEquiv 2 ℝ ({w : InfinitePlace K // IsReal w} → ℝ)).symm).prodCongr
      ((WithLp.linearEquiv 2 ℝ ({w : InfinitePlace K // IsComplex w} → ℂ)).trans <|
        (LinearEquiv.piCongrRight fun w : {w : InfinitePlace K // IsComplex w} =>
            cmulEquiv (c w.1) (hc w.1)).trans
          (WithLp.linearEquiv 2 ℝ ({w : InfinitePlace K // IsComplex w} → ℂ)).symm)).trans
      (WithLp.linearEquiv 2 ℝ _).symm)

variable (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)

private theorem placeScale_apply_fst (x : euclidean.mixedSpace K) (v : {w : InfinitePlace K // IsReal w}) :
    (placeScale K c hc x).fst v = c v.1 * x.fst v := by
  simp [placeScale, mulEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.piCongrRight_apply]

private theorem placeScale_apply_snd (x : euclidean.mixedSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (placeScale K c hc x).snd w = ((c w.1 : ℝ) : ℂ) * x.snd w := by
  simp [placeScale, cmulEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.piCongrRight_apply]

private theorem placeScale_symm_apply_fst (x : euclidean.mixedSpace K) (v : {w : InfinitePlace K // IsReal w}) :
    ((placeScale K c hc).symm x).fst v = x.fst v / c v.1 := by
  have h := placeScale_apply_fst K c hc ((placeScale K c hc).symm x) v
  rw [LinearEquiv.apply_symm_apply] at h
  have h0 : c v.1 ≠ 0 := (hc v.1).ne'
  field_simp
  linarith [h]

private theorem placeScale_symm_apply_snd (x : euclidean.mixedSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    ((placeScale K c hc).symm x).snd w = x.snd w / ((c w.1 : ℝ) : ℂ) := by
  have h := placeScale_apply_snd K c hc ((placeScale K c hc).symm x) w
  rw [LinearEquiv.apply_symm_apply] at h
  have h0 : ((c w.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hc w.1).ne'
  rw [eq_div_iff h0, mul_comm]
  exact h.symm

private def scaleDiag : index K → ℝ :=
  Sum.elim (fun v => c v.1) (fun p => c p.1.1)

private theorem euclideanRepr_placeScale (x : euclidean.mixedSpace K) (i : index K) :
    (euclidean.stdOrthonormalBasis K).repr (placeScale K c hc x) i
      = scaleDiag K c i * (euclidean.stdOrthonormalBasis K).repr x i := by
  rcases i with v | ⟨w, k⟩
  · simp [scaleDiag, euclideanRepr_inl, placeScale_apply_fst]
  · fin_cases k
    · simp [scaleDiag, euclideanRepr_inr_re, placeScale_apply_snd]
    · simp [scaleDiag, euclideanRepr_inr_im, placeScale_apply_snd]

private theorem prod_scaleDiag : ∏ i : index K, scaleDiag K c i = ∏ w : InfinitePlace K, c w ^ mult w := by
  rw [Fintype.prod_sum_type, prod_eq_prod_mul_prod]
  have h1 : (∏ v : {w : InfinitePlace K // IsReal w}, scaleDiag K c (Sum.inl v))
      = ∏ v : {w : InfinitePlace K // IsReal w}, c v.1 ^ mult v.1 :=
    Finset.prod_congr rfl fun v _ => by rw [mult_isReal, pow_one]; rfl
  have h2 : (∏ p : {w : InfinitePlace K // IsComplex w} × Fin 2, scaleDiag K c (Sum.inr p))
      = ∏ w : {w : InfinitePlace K // IsComplex w}, c w.1 ^ mult w.1 := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Fin.prod_univ_two, mult_isComplex, sq]
    rfl
  rw [h1, h2]

private theorem prod_pow_mult_pos (d : InfinitePlace K → ℝ) (hd : ∀ w, 0 < d w) :
    0 < ∏ w : InfinitePlace K, d w ^ mult w :=
  Finset.prod_pos fun w _ => pow_pos (hd w) _

private theorem inner_placeScale (x y : euclidean.mixedSpace K) :
    inner ℝ (placeScale K c hc x) y = inner ℝ x (placeScale K c hc y) := by
  rw [← (euclidean.stdOrthonormalBasis K).sum_inner_mul_inner (placeScale K c hc x) y,
    ← (euclidean.stdOrthonormalBasis K).sum_inner_mul_inner x (placeScale K c hc y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : ∀ z : euclidean.mixedSpace K,
      (inner ℝ z ((euclidean.stdOrthonormalBasis K) i) : ℝ)
        = (euclidean.stdOrthonormalBasis K).repr z i := fun z => by
    rw [real_inner_comm, OrthonormalBasis.repr_apply_apply]
  have hl : ∀ z : euclidean.mixedSpace K,
      (inner ℝ ((euclidean.stdOrthonormalBasis K) i) z : ℝ)
        = (euclidean.stdOrthonormalBasis K).repr z i := fun z => by
    rw [OrthonormalBasis.repr_apply_apply]
  rw [hr, hr, hl, hl, euclideanRepr_placeScale, euclideanRepr_placeScale]
  ring

variable (L : Submodule ℤ (euclidean.mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]

private abbrev scaleLattice : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ L (placeScale K c hc).toContinuousLinearEquiv.symm.toLinearMap

private theorem mem_scaleLattice (z : euclidean.mixedSpace K) :
    z ∈ scaleLattice K c hc L ↔ (placeScale K c hc).symm z ∈ L :=
  Iff.rfl

private theorem mem_comap_placeScale (N : Submodule ℤ (euclidean.mixedSpace K)) (z : euclidean.mixedSpace K) :
    z ∈ ZLattice.comap ℝ N (placeScale K c hc).toContinuousLinearEquiv.toLinearMap
      ↔ placeScale K c hc z ∈ N :=
  Iff.rfl

private theorem dualSubmodule_scaleLattice :
    LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) (scaleLattice K c hc L)
      = ZLattice.comap ℝ
          (LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) L)
          (placeScale K c hc).toContinuousLinearEquiv.toLinearMap := by
  ext y
  rw [LinearMap.BilinForm.mem_dualSubmodule, mem_comap_placeScale,
    LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro h w hw
    have hz : placeScale K c hc w ∈ scaleLattice K c hc L := by
      rw [mem_scaleLattice]
      simpa using hw
    have h1 := h _ hz
    rw [innerₗ_apply_apply] at h1 ⊢
    rw [inner_placeScale K c hc y w]
    exact h1
  · intro h z hz
    rw [mem_scaleLattice] at hz
    have h1 := h _ hz
    rw [innerₗ_apply_apply] at h1 ⊢
    have hzz : z = placeScale K c hc ((placeScale K c hc).symm z) := by simp
    rw [hzz, ← inner_placeScale K c hc y ((placeScale K c hc).symm z)]
    exact h1

set_option maxHeartbeats 3200000 in

private theorem covolume_scaleLattice :
    ZLattice.covolume (scaleLattice K c hc L) volume
      = (∏ w : InfinitePlace K, c w ^ mult w) * ZLattice.covolume L volume := by
  classical
  let b : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let bJ : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ (scaleLattice K c hc L) :=
    b.ofZLatticeComap ℝ L (placeScale K c hc).toContinuousLinearEquiv.symm.toLinearEquiv
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Fintype.card (index K) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (↥L)]
    rw [show Module.finrank ℤ (↥L) = Module.finrank ℝ (euclidean.mixedSpace K) from ZLattice.rank ℝ L]
    rw [Module.finrank_eq_card_basis (euclidean.stdOrthonormalBasis K).toBasis]
  let e' : Module.Free.ChooseBasisIndex ℤ L ≃ index K := Fintype.equivOfCardEq hcard
  let o : OrthonormalBasis (Module.Free.ChooseBasisIndex ℤ L) ℝ (euclidean.mixedSpace K) :=
    (euclidean.stdOrthonormalBasis K).reindex e'.symm
  have hrepr : ∀ (x : euclidean.mixedSpace K) i,
      o.repr x i = (euclidean.stdOrthonormalBasis K).repr x (e' i) := by
    intro x i
    rw [show o = (euclidean.stdOrthonormalBasis K).reindex e'.symm from rfl,
      OrthonormalBasis.repr_reindex]
    simp
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped (b := o.toBasis) volume)]
    rw [measureReal_def,
      show parallelepiped ⇑(o.toBasis) = parallelepiped ⇑o from by rw [OrthonormalBasis.coe_toBasis],
      o.volume_parallelepiped]
    exact ENNReal.toReal_one
  have hbJcoe : ∀ k, ((bJ k : scaleLattice K c hc L) : euclidean.mixedSpace K)
      = placeScale K c hc ((b k : L) : _) := by
    intro k
    rw [show bJ = b.ofZLatticeComap ℝ L (placeScale K c hc).toContinuousLinearEquiv.symm.toLinearEquiv
      from rfl]
    rw [Module.Basis.ofZLatticeComap_apply]
    rfl
  have hmat : o.toBasis.toMatrix (fun k => ((bJ k : _) : euclidean.mixedSpace K))
      = Matrix.diagonal (fun i => scaleDiag K c (e' i))
          * o.toBasis.toMatrix (fun k => ((b k : L) : _)) := by
    ext i k
    rw [Matrix.diagonal_mul, Basis.toMatrix_apply, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis_repr_apply, hrepr, hrepr,
      hbJcoe, euclideanRepr_placeScale]
  have hdet : o.toBasis.det (fun k => ((bJ k : _) : euclidean.mixedSpace K))
      = (∏ w : InfinitePlace K, c w ^ mult w) * o.toBasis.det (fun k => ((b k : L) : _)) := by
    rw [Basis.det_apply, Basis.det_apply, hmat, Matrix.det_mul, Matrix.det_diagonal]
    congr 1
    rw [Equiv.prod_comp e' (scaleDiag K c)]
    exact prod_scaleDiag K c
  have hJL : ZLattice.covolume (scaleLattice K c hc L) volume
      = |o.toBasis.det (fun k => ((bJ k : _) : euclidean.mixedSpace K))| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal (b := bJ) (b₀ := o.toBasis) (μ := volume), hvol, mul_one]
    rfl
  have hL : ZLattice.covolume L volume = |o.toBasis.det (fun k => ((b k : L) : _))| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal (b := b) (b₀ := o.toBasis) (μ := volume), hvol, mul_one]
    rfl
  rw [hJL, hdet, abs_mul, hL, abs_of_pos (prod_pow_mult_pos K c hc)]

private def torusNorm (t : realSpace K) : ℝ := ∏ w : InfinitePlace K, t w ^ mult w

private theorem torusNorm_pos {t : realSpace K} (ht : ∀ w, 0 < t w) : 0 < torusNorm K t :=
  Finset.prod_pos fun w _ => pow_pos (ht w) _

private theorem torusNorm_inv (t : realSpace K) : torusNorm K t⁻¹ = (torusNorm K t)⁻¹ := by
  simp only [torusNorm, Pi.inv_apply, inv_pow, Finset.prod_inv_distrib]

private def torusForm (t : realSpace K) (x : mixedSpace K) : ℝ :=
  ∑ w : InfinitePlace K, (mult w : ℝ) * t w * normAtPlace w x ^ 2

private def torusFormCoord (t : realSpace K) (v : euclidean.mixedSpace K) : ℝ :=
  (∑ w : {w : InfinitePlace K // IsReal w}, t w.1 * (v.fst w) ^ 2)
    + ∑ w : {w : InfinitePlace K // IsComplex w}, 2 * t w.1 * Complex.normSq (v.snd w)

private theorem torusForm_toMixed (t : realSpace K) (v : euclidean.mixedSpace K) :
    torusForm K t (euclidean.toMixed K v) = torusFormCoord K t v := by
  rw [torusForm, torusFormCoord, sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, normAtPlace_apply_of_isReal w.2, Nat.cast_one, one_mul, Real.norm_eq_abs, sq_abs]
    rfl
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, Nat.cast_ofNat, Complex.sq_norm]
    rfl

private def unitTorus (u : (𝓞 K)ˣ) (t : realSpace K) : realSpace K :=
  fun w => (w ((u : 𝓞 K) : K)) ^ 2 * t w

private theorem unitTorus_apply (u : (𝓞 K)ˣ) (t : realSpace K) (w : InfinitePlace K) :
    unitTorus K u t w = (w ((u : 𝓞 K) : K)) ^ 2 * t w := rfl

private theorem torusForm_unitSMul (u : (𝓞 K)ˣ) (t : realSpace K) (x : mixedSpace K) :
    torusForm K t (u • x) = torusForm K (unitTorus K u t) x := by
  rw [torusForm, torusForm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [unitSMul_smul, map_mul, normAtPlace_apply, unitTorus_apply]
  ring

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_TorusTheta
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_TorusFold

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace NumberField.Units MeasureTheory Set
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

variable (K : Type) [Field K] [NumberField K]

private def foldBox : Set (realSpace K) :=
  {x | ∀ w : InfinitePlace K, w ≠ dirichletUnitTheorem.w₀ → x w ∈ Ico (0 : ℝ) 2}

private def foldDomain : Set (realSpace K) :=
  fundamentalCone.expMapBasis '' foldBox K

private def torusHaar : Measure (realSpace K) :=
  volume.withDensity (fun t => ∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹)

private theorem torusNorm_expMapBasis (x : realSpace K) :
    torusNorm K (fundamentalCone.expMapBasis x)
      = Real.exp (x dirichletUnitTheorem.w₀) ^ Module.finrank ℚ K := by
  rw [torusNorm]; exact fundamentalCone.prod_expMapBasis_pow x

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_TorusFold
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_TorusFeeders

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

p2m_open "Real MeasureTheory Set Filter Function Topology Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

open scoped nonZeroDivisors RealInnerProductSpace Classical

variable (K : Type) [Field K] [NumberField K]

private theorem continuous_torusNorm : Continuous (torusNorm K) := by
  unfold torusNorm
  exact continuous_finsetProd _ fun w _ => (continuous_apply w).pow _

private theorem measurable_torusNorm : Measurable (torusNorm K) :=
  (continuous_torusNorm K).measurable

private theorem prod_pow_mult_unit (u : (𝓞 K)ˣ) :
    ∏ w : InfinitePlace K, (w ((u : 𝓞 K) : K)) ^ mult w = 1 := by
  have h := norm_unit (K := K) u
  rw [mixedEmbedding.norm_apply] at h
  simpa only [normAtPlace_apply] using h

private theorem torusNorm_unitTorus (u : (𝓞 K)ˣ) (t : realSpace K) :
    torusNorm K (unitTorus K u t) = torusNorm K t := by
  unfold torusNorm
  simp_rw [unitTorus_apply, mul_pow, Finset.prod_mul_distrib, ← pow_mul, mul_comm 2, pow_mul,
    Finset.prod_pow, prod_pow_mult_unit, one_pow, one_mul]

private theorem unitTorus_one (t : realSpace K) : unitTorus K 1 t = t := by
  funext w
  rw [unitTorus_apply, Units.val_one, NumberField.RingOfIntegers.coe_eq_algebraMap, map_one, map_one, one_pow,
    one_mul]

private theorem unitTorus_mul (u u' : (𝓞 K)ˣ) (t : realSpace K) :
    unitTorus K (u * u') t = unitTorus K u (unitTorus K u' t) := by
  funext w
  rw [unitTorus_apply, unitTorus_apply, unitTorus_apply, Units.val_mul,
    NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
    NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, mul_pow, mul_assoc]

private theorem torusForm_mono {t t' : realSpace K} (h : t ≤ t') (x : mixedSpace K) :
    torusForm K t x ≤ torusForm K t' x := by
  unfold torusForm
  refine Finset.sum_le_sum fun w _ => ?_
  have hm : (0 : ℝ) ≤ mult w := by exact_mod_cast (mult_pos (w := w)).le
  have hn : 0 ≤ normAtPlace w x ^ 2 := sq_nonneg _
  have := h w
  nlinarith [mul_nonneg hm hn]

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_TorusFeeders
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_TorusTiling

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory Set
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

variable (K : Type) [Field K] [NumberField K]

private def orthant : Set (realSpace K) := {t | ∀ w, 0 < t w}

omit [NumberField K] in
private theorem orthant_def : orthant K = {t : realSpace K | ∀ w, 0 < t w} := rfl

variable {K} in
omit [NumberField K] in
private theorem mem_orthant {t : realSpace K} : t ∈ orthant K ↔ ∀ w, 0 < t w := Iff.rfl

private theorem measurableSet_orthant : MeasurableSet (orthant K) := by
  have : orthant K = ⋂ w, {t : realSpace K | 0 < t w} := by
    ext t; simp only [mem_orthant, mem_iInter, mem_setOf_eq]
  rw [this]
  exact MeasurableSet.iInter fun w => measurableSet_lt measurable_const (measurable_pi_apply w)

private theorem expMapBasis_add (x y : realSpace K) :
    expMapBasis (x + y) = expMapBasis x * expMapBasis y := by
  rw [expMapBasis_apply, expMapBasis_apply, expMapBasis_apply, map_add, expMap_add]

private theorem expMapBasis_zero : expMapBasis (0 : realSpace K) = 1 := by
  have h := expMapBasis_add K 0 0
  rw [add_zero] at h
  funext w
  have hw := congrFun h w
  rw [Pi.mul_apply] at hw
  have hp : 0 < expMapBasis (0 : realSpace K) w := expMapBasis_pos _ _
  rw [Pi.one_apply]
  nlinarith [hw, hp]

private theorem expMapBasis_mem_orthant (x : realSpace K) : expMapBasis x ∈ orthant K :=
  fun w => expMapBasis_pos x w

private theorem range_expMapBasis : range (expMapBasis : realSpace K → realSpace K) = orthant K := by
  refine Subset.antisymm (range_subset_iff.mpr (expMapBasis_mem_orthant K)) fun t ht => ?_
  refine ⟨(completeBasis K).equivFun (expMap.symm t), ?_⟩
  rw [expMapBasis_apply, LinearEquiv.symm_apply_apply]
  exact expMap.right_inv (by rw [expMap_target]; exact mem_univ_pi.mpr ht)

private theorem image_expMapBasis_univ : expMapBasis '' (univ : Set (realSpace K)) = orthant K := by
  rw [image_univ, range_expMapBasis]

private theorem exists_eq_expMapBasis {c : realSpace K} (hc : c ∈ orthant K) : ∃ y, c = expMapBasis y := by
  obtain ⟨y, hy⟩ := (range_expMapBasis K).symm.subset hc
  exact ⟨y, hy.symm⟩

private theorem measurableEmbedding_expMapBasis :
    MeasurableEmbedding (expMapBasis : realSpace K → realSpace K) :=
  (expMapBasis.to_isOpenEmbedding (expMapBasis_source K)).measurableEmbedding

private theorem measurable_expMapBasis : Measurable (expMapBasis : realSpace K → realSpace K) :=
  (continuous_expMapBasis K).measurable

private theorem measurableSet_foldBox : MeasurableSet (foldBox K) := by
  have : foldBox K = ⋂ w : {w : InfinitePlace K // w ≠ w₀},
      (fun x : realSpace K => x w.1) ⁻¹' Ico (0 : ℝ) 2 := by
    ext x
    simp only [foldBox, mem_setOf_eq, mem_iInter, mem_preimage, Subtype.forall]
  rw [this]
  exact MeasurableSet.iInter fun w => measurableSet_Ico.preimage (measurable_pi_apply w.1)

private theorem measurableSet_foldDomain : MeasurableSet (foldDomain K) :=
  (measurableEmbedding_expMapBasis K).measurableSet_image.mpr (measurableSet_foldBox K)

private theorem foldDomain_subset_orthant : foldDomain K ⊆ orthant K := by
  rintro _ ⟨x, _, rfl⟩
  exact expMapBasis_mem_orthant K x

private theorem torusHaar_def :
    torusHaar K = volume.withDensity (fun t : realSpace K => ∏ w, ENNReal.ofReal (t w)⁻¹) := rfl

private theorem measurable_torusDensity :
    Measurable fun t : realSpace K => ∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹ :=
  Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w).inv

private theorem torusDensity_eq_zero_of_not_mem {t : realSpace K} (ht : t ∉ orthant K) :
    ∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹ = 0 := by
  simp only [mem_orthant, not_forall, not_lt] at ht
  obtain ⟨w, hw⟩ := ht
  exact Finset.prod_eq_zero (Finset.mem_univ w) (ENNReal.ofReal_eq_zero.mpr (inv_nonpos.mpr hw))

private theorem torusDensity_eq_indicator :
    (fun t : realSpace K => ∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹)
      = (orthant K).indicator fun t => ∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹ := by
  funext t
  by_cases ht : t ∈ orthant K
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht, torusDensity_eq_zero_of_not_mem K ht]

private theorem torusHaar_restrict_orthant : (torusHaar K).restrict (orthant K) = torusHaar K := by
  conv_rhs => rw [torusHaar_def, torusDensity_eq_indicator,
    withDensity_indicator (measurableSet_orthant K)]
  rw [torusHaar_def, restrict_withDensity (measurableSet_orthant K)]

private theorem setLIntegral_orthant_torusHaar (g : realSpace K → ℝ≥0∞) :
    ∫⁻ t in orthant K, g t ∂(torusHaar K) = ∫⁻ t, g t ∂(torusHaar K) := by
  rw [torusHaar_restrict_orthant]

private def foldConst : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K * ENNReal.ofReal (regulator K)

private theorem foldConst_ne_top : foldConst K ≠ ∞ := by
  unfold foldConst
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero))
    (ENNReal.natCast_ne_top _)) ENNReal.ofReal_ne_top

private theorem exp_mul_finrank_eq_prod_mul_prod (x : realSpace K) :
    Real.exp (x w₀ * Module.finrank ℚ K)
      = (∏ w : InfinitePlace K, expMapBasis x w) *
          ∏ w : {w : InfinitePlace K // IsComplex w}, expMapBasis x w.1 := by
  rw [Real.exp_mul, Real.rpow_natCast, ← prod_expMapBasis_pow x,
    prod_eq_prod_mul_prod (fun w => expMapBasis x w ^ w.mult),
    prod_eq_prod_mul_prod (fun w => expMapBasis x w)]
  simp only [mult_isReal, mult_isComplex, pow_one]
  rw [Finset.prod_pow, sq, mul_assoc]

private theorem jacobian_mul_torusDensity (x : realSpace K) :
    ENNReal.ofReal (Real.exp (x w₀ * Module.finrank ℚ K)) *
      (∏ i : {w : InfinitePlace K // IsComplex w}, .ofReal (expMapBasis (fun w ↦ x w) i))⁻¹ *
        ∏ w : InfinitePlace K, ENNReal.ofReal (expMapBasis x w)⁻¹ = 1 := by
  have hx : (fun w ↦ x w) = x := rfl
  rw [hx]
  have ha : ∀ w, 0 < expMapBasis x w := expMapBasis_pos x
  have hcx : 0 < ∏ w : {w : InfinitePlace K // IsComplex w}, expMapBasis x w.1 :=
    Finset.prod_pos fun w _ => ha w.1
  have hall : 0 < ∏ w : InfinitePlace K, expMapBasis x w := Finset.prod_pos fun w _ => ha w
  have h3 : ∏ w : InfinitePlace K, ENNReal.ofReal (expMapBasis x w)⁻¹
      = ENNReal.ofReal (∏ w : InfinitePlace K, expMapBasis x w)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ENNReal.ofReal_prod_of_nonneg fun w _ => inv_nonneg.mpr (ha w).le]
  rw [h3, ← ENNReal.ofReal_prod_of_nonneg fun w _ => (ha w.1).le, ← ENNReal.ofReal_inv_of_pos hcx,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr hcx.le)),
    exp_mul_finrank_eq_prod_mul_prod, ← ENNReal.ofReal_one]
  congr 1
  field_simp

private theorem setLIntegral_image_expMapBasis_torusHaar {s : Set (realSpace K)} (hs : MeasurableSet s)
    {g : realSpace K → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t in expMapBasis '' s, g t ∂(torusHaar K)
      = (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K * ENNReal.ofReal (regulator K) *
          ∫⁻ x in s, g (expMapBasis x) := by
  have hdg : Measurable ((fun t : realSpace K => ∏ w, ENNReal.ofReal (t w)⁻¹) * g) :=
    (measurable_torusDensity K).mul hg
  rw [torusHaar_def, setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_torusDensity K) hg
    ((measurableEmbedding_expMapBasis K).measurableSet_image.mpr hs),
    setLIntegral_expMapBasis_image hs hdg, mul_right_comm (((2 : ℝ≥0∞)⁻¹) ^ nrComplexPlaces K)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Pi.mul_apply, ← mul_assoc, jacobian_mul_torusDensity, one_mul]

private theorem setLIntegral_image_expMapBasis_torusHaar' {s : Set (realSpace K)} (hs : MeasurableSet s)
    {g : realSpace K → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t in expMapBasis '' s, g t ∂(torusHaar K) = foldConst K * ∫⁻ x in s, g (expMapBasis x) :=
  setLIntegral_image_expMapBasis_torusHaar K hs hg

private theorem lintegral_torusHaar_eq {g : realSpace K → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g t ∂(torusHaar K) = foldConst K * ∫⁻ x, g (expMapBasis x) := by
  rw [← setLIntegral_orthant_torusHaar, ← image_expMapBasis_univ,
    setLIntegral_image_expMapBasis_torusHaar' K MeasurableSet.univ hg, Measure.restrict_univ]

private def shift (k : Fin (rank K) → ℤ) : realSpace K :=
  fun w => if h : w = w₀ then 0 else 2 * (k (equivFinRank.symm ⟨w, h⟩) : ℝ)

private theorem shift_apply_w₀ (k : Fin (rank K) → ℤ) : shift K k w₀ = 0 := by
  simp [shift]

private theorem shift_apply_of_ne (k : Fin (rank K) → ℤ) {w : InfinitePlace K} (hw : w ≠ w₀) :
    shift K k w = 2 * (k (equivFinRank.symm ⟨w, hw⟩) : ℝ) := by
  simp [shift, hw]

private theorem shift_apply_equivFinRank (k : Fin (rank K) → ℤ) (i : Fin (rank K)) :
    shift K k (equivFinRank i) = 2 * (k i : ℝ) := by
  rw [shift_apply_of_ne K k (equivFinRank i).2, Subtype.coe_eta, Equiv.symm_apply_apply]

private theorem shift_zero : shift K 0 = 0 := by
  funext w
  by_cases hw : w = w₀
  · subst hw; rw [shift_apply_w₀]; rfl
  · rw [shift_apply_of_ne K 0 hw]; simp

private theorem shift_add (k k' : Fin (rank K) → ℤ) : shift K (k + k') = shift K k + shift K k' := by
  funext w
  by_cases hw : w = w₀
  · subst hw; simp [shift_apply_w₀]
  · rw [Pi.add_apply, shift_apply_of_ne K _ hw, shift_apply_of_ne K _ hw, shift_apply_of_ne K _ hw,
      Pi.add_apply]
    push_cast
    ring

private def boxIndex (x : realSpace K) : Fin (rank K) → ℤ := fun i => ⌊x (equivFinRank i) / 2⌋

private theorem sub_shift_mem_foldBox_iff (x : realSpace K) (k : Fin (rank K) → ℤ) :
    x - shift K k ∈ foldBox K ↔ k = boxIndex K x := by
  constructor
  · intro h
    funext i
    have hi := h (equivFinRank i) (equivFinRank i).2
    rw [Pi.sub_apply, shift_apply_equivFinRank, mem_Ico] at hi
    rw [boxIndex, eq_comm, Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ (two_pos : (0 : ℝ) < 2)]; linarith [hi.1]
    · rw [div_lt_iff₀ (two_pos : (0 : ℝ) < 2)]; linarith [hi.2]
  · rintro rfl w hw
    rw [Pi.sub_apply, shift_apply_of_ne K _ hw, mem_Ico, boxIndex]
    set i := equivFinRank.symm ⟨w, hw⟩ with hi
    have hwi : (equivFinRank i : InfinitePlace K) = w := by rw [hi, Equiv.apply_symm_apply]
    rw [hwi]
    constructor
    · have := Int.sub_floor_div_mul_nonneg (x w) (two_pos : (0 : ℝ) < 2); linarith
    · have := Int.sub_floor_div_mul_lt (x w) (two_pos : (0 : ℝ) < 2); linarith

private theorem sub_shift_boxIndex_mem_foldBox (x : realSpace K) : x - shift K (boxIndex K x) ∈ foldBox K :=
  (sub_shift_mem_foldBox_iff K x _).mpr rfl

private def boxPiece (k : Fin (rank K) → ℤ) : Set (realSpace K) := (fun x => x + shift K k) '' foldBox K

private theorem mem_boxPiece {k : Fin (rank K) → ℤ} {x : realSpace K} :
    x ∈ boxPiece K k ↔ x - shift K k ∈ foldBox K := by
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [add_sub_cancel_right]
  · intro h; exact ⟨x - shift K k, h, sub_add_cancel _ _⟩

private theorem boxPiece_eq_preimage (k : Fin (rank K) → ℤ) :
    boxPiece K k = (fun x => x - shift K k) ⁻¹' foldBox K := by
  ext x; rw [mem_boxPiece, mem_preimage]

private theorem measurableSet_boxPiece (k : Fin (rank K) → ℤ) : MeasurableSet (boxPiece K k) := by
  rw [boxPiece_eq_preimage]
  exact (measurableSet_foldBox K).preimage (measurable_sub_const _)

private theorem pairwise_disjoint_boxPiece : Pairwise (Function.onFun Disjoint (boxPiece K)) := by
  intro k k' hkk'
  refine disjoint_left.mpr fun x hx hx' => hkk' ?_
  rw [mem_boxPiece, sub_shift_mem_foldBox_iff] at hx hx'
  rw [hx, hx']

private theorem iUnion_boxPiece : ⋃ k, boxPiece K k = univ :=
  eq_univ_of_forall fun x => mem_iUnion.mpr ⟨boxIndex K x, (mem_boxPiece K).mpr (sub_shift_boxIndex_mem_foldBox K x)⟩

private def unitPow (k : Fin (rank K) → ℤ) : (𝓞 K)ˣ := ∏ i, fundSystem K i ^ k i

private theorem unitPow_zero : unitPow K 0 = 1 := by simp [unitPow]

private theorem unitPow_add (k k' : Fin (rank K) → ℤ) : unitPow K (k + k') = unitPow K k * unitPow K k' := by
  simp [unitPow, zpow_add, Finset.prod_mul_distrib]

private def placeHom (w : InfinitePlace K) : (𝓞 K)ˣ →* ℝ :=
  (w.1.toMonoidWithZeroHom.toMonoidHom).comp
    ((Units.coeHom K).comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom))

omit [NumberField K] in
private theorem placeHom_apply (w : InfinitePlace K) (u : (𝓞 K)ˣ) : placeHom K w u = w ((u : 𝓞 K) : K) := rfl

private theorem place_unitPow (w : InfinitePlace K) (k : Fin (rank K) → ℤ) :
    w ((unitPow K k : 𝓞 K) : K) = ∏ i, w ((fundSystem K i : 𝓞 K) : K) ^ k i := by
  rw [← placeHom_apply, unitPow, map_prod]
  simp_rw [map_zpow, placeHom_apply]

omit [NumberField K] in
private theorem place_unit_pos (w : InfinitePlace K) (u : (𝓞 K)ˣ) : 0 < w ((u : 𝓞 K) : K) :=
  (w.1.pos_iff).mpr (by simp)

private theorem expMapBasis_shift (k : Fin (rank K) → ℤ) :
    expMapBasis (shift K k) = fun w => (w ((unitPow K k : 𝓞 K) : K)) ^ 2 := by
  funext w
  rw [expMapBasis_apply', Pi.smul_apply, smul_eq_mul, shift_apply_w₀, Real.exp_zero, one_mul,
    place_unitPow, ← Finset.prod_pow]
  refine Fintype.prod_equiv equivFinRank.symm _ _ fun i => ?_
  have hs : shift K k i.1 = 2 * (k (equivFinRank.symm i) : ℝ) := shift_apply_of_ne K k i.2
  rw [hs, show (2 * (k (equivFinRank.symm i) : ℝ)) = ((k (equivFinRank.symm i) * 2 : ℤ) : ℝ) by
    push_cast; ring, Real.rpow_intCast, zpow_mul, zpow_two, ← pow_two]

private theorem unitTorus_unitPow_expMapBasis (k : Fin (rank K) → ℤ) (x : realSpace K) :
    unitTorus K (unitPow K k) (expMapBasis x) = expMapBasis (x + shift K k) := by
  rw [expMapBasis_add, expMapBasis_shift]
  funext w
  rw [unitTorus_apply, Pi.mul_apply, mul_comm]

private theorem measurable_mul_left (c : realSpace K) : Measurable fun t : realSpace K => c * t :=
  (continuous_const.mul continuous_id).measurable

private def scaleEquiv {c : realSpace K} (hc : c ∈ orthant K) : realSpace K ≃ᵐ realSpace K :=
  MeasurableEquiv.piCongrRight fun w => MeasurableEquiv.mulLeft₀ (c w) (hc w).ne'

omit [NumberField K] in
private theorem coe_scaleEquiv {c : realSpace K} (hc : c ∈ orthant K) :
    ⇑(scaleEquiv K hc) = fun t => c * t := rfl

omit [NumberField K] in
private theorem measurableEmbedding_mul_left {c : realSpace K} (hc : c ∈ orthant K) :
    MeasurableEmbedding fun t : realSpace K => c * t := by
  rw [← coe_scaleEquiv K hc]
  exact (scaleEquiv K hc).measurableEmbedding

private theorem lintegral_comp_mul_left {c : realSpace K} (hc : c ∈ orthant K) {g : realSpace K → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ t, g (c * t) ∂(torusHaar K) = ∫⁻ t, g t ∂(torusHaar K) := by
  obtain ⟨y, rfl⟩ := exists_eq_expMapBasis K hc
  have hgm : Measurable fun t => g (expMapBasis y * t) := hg.comp (measurable_mul_left K _)
  rw [lintegral_torusHaar_eq K hgm, lintegral_torusHaar_eq K hg]
  congr 1
  simp_rw [← expMapBasis_add]
  exact lintegral_add_left_eq_self (fun x => g (expMapBasis x)) y

private theorem map_mul_left_torusHaar {c : realSpace K} (hc : c ∈ orthant K) :
    (torusHaar K).map (fun t => c * t) = torusHaar K := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_mul_left K c) hA, ← lintegral_indicator_one hA,
    ← lintegral_indicator_one (measurable_mul_left K c hA),
    ← lintegral_comp_mul_left K hc (measurable_one.indicator hA)]
  rfl

private theorem measurePreserving_mul_left {c : realSpace K} (hc : c ∈ orthant K) :
    MeasurePreserving (fun t => c * t) (torusHaar K) (torusHaar K) :=
  ⟨measurable_mul_left K c, map_mul_left_torusHaar K hc⟩

private def unitScale (u : (𝓞 K)ˣ) : realSpace K := fun w => (w ((u : 𝓞 K) : K)) ^ 2

omit [NumberField K] in
private theorem unitScale_mem_orthant (u : (𝓞 K)ˣ) : unitScale K u ∈ orthant K :=
  fun w => pow_pos (place_unit_pos K w u) 2

omit [NumberField K] in
private theorem unitTorus_eq_mul (u : (𝓞 K)ˣ) : unitTorus K u = fun t => unitScale K u * t := rfl

private theorem measurePreserving_unitTorus (u : (𝓞 K)ˣ) :
    MeasurePreserving (unitTorus K u) (torusHaar K) (torusHaar K) := by
  rw [unitTorus_eq_mul]; exact measurePreserving_mul_left K (unitScale_mem_orthant K u)

omit [NumberField K] in
private theorem measurableEmbedding_unitTorus (u : (𝓞 K)ˣ) : MeasurableEmbedding (unitTorus K u) := by
  rw [unitTorus_eq_mul]; exact measurableEmbedding_mul_left K (unitScale_mem_orthant K u)

omit [NumberField K] in
private theorem measurable_unitTorus (u : (𝓞 K)ˣ) : Measurable (unitTorus K u) :=
  (measurableEmbedding_unitTorus K u).measurable

private theorem setLIntegral_image_unitTorus (u : (𝓞 K)ˣ) (g : realSpace K → ℝ≥0∞) (A : Set (realSpace K)) :
    ∫⁻ t in unitTorus K u '' A, g t ∂(torusHaar K) = ∫⁻ t in A, g (unitTorus K u t) ∂(torusHaar K) :=
  ((measurePreserving_unitTorus K u).setLIntegral_comp_emb (measurableEmbedding_unitTorus K u) g A).symm

private theorem setIntegral_image_unitTorus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : (𝓞 K)ˣ) (h : realSpace K → E) (A : Set (realSpace K)) :
    ∫ t in unitTorus K u '' A, h t ∂(torusHaar K) = ∫ t in A, h (unitTorus K u t) ∂(torusHaar K) :=
  (measurePreserving_unitTorus K u).setIntegral_image_emb (measurableEmbedding_unitTorus K u) h A

private def foldPiece (k : Fin (rank K) → ℤ) : Set (realSpace K) := unitTorus K (unitPow K k) '' foldDomain K

private theorem foldPiece_eq_image_boxPiece (k : Fin (rank K) → ℤ) :
    foldPiece K k = expMapBasis '' boxPiece K k := by
  rw [foldPiece, foldDomain, boxPiece, image_image, image_image]
  refine image_congr fun x _ => ?_
  exact unitTorus_unitPow_expMapBasis K k x

private theorem measurableSet_foldPiece (k : Fin (rank K) → ℤ) : MeasurableSet (foldPiece K k) := by
  rw [foldPiece_eq_image_boxPiece]
  exact (measurableEmbedding_expMapBasis K).measurableSet_image.mpr (measurableSet_boxPiece K k)

private theorem pairwise_disjoint_foldPiece : Pairwise (Function.onFun Disjoint (foldPiece K)) := by
  intro k k' hkk'
  show Disjoint (foldPiece K k) (foldPiece K k')
  rw [foldPiece_eq_image_boxPiece, foldPiece_eq_image_boxPiece]
  exact (disjoint_image_iff (injective_expMapBasis K)).mpr (pairwise_disjoint_boxPiece K hkk')

private theorem iUnion_foldPiece : ⋃ k, foldPiece K k = orthant K := by
  simp_rw [foldPiece_eq_image_boxPiece, ← image_iUnion, iUnion_boxPiece, image_expMapBasis_univ]

private theorem setLIntegral_orthant_eq_tsum_foldDomain (g : realSpace K → ℝ≥0∞) :
    ∫⁻ t in orthant K, g t ∂(torusHaar K)
      = ∑' k : Fin (rank K) → ℤ, ∫⁻ t in foldDomain K, g (unitTorus K (unitPow K k) t) ∂(torusHaar K) := by
  rw [← iUnion_foldPiece K, lintegral_iUnion (measurableSet_foldPiece K) (pairwise_disjoint_foldPiece K)]
  exact tsum_congr fun k => setLIntegral_image_unitTorus K _ g _

private theorem hasSum_setIntegral_foldDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : realSpace K → E} (hh : IntegrableOn h (orthant K) (torusHaar K)) :
    HasSum (fun k : Fin (rank K) → ℤ => ∫ t in foldDomain K, h (unitTorus K (unitPow K k) t) ∂(torusHaar K))
      (∫ t in orthant K, h t ∂(torusHaar K)) := by
  have := hasSum_integral_iUnion (μ := torusHaar K) (f := h) (measurableSet_foldPiece K)
    (pairwise_disjoint_foldPiece K) ((iUnion_foldPiece K).symm ▸ hh)
  rw [iUnion_foldPiece] at this
  convert this using 2 with k
  exact (setIntegral_image_unitTorus K _ h _).symm

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_TorusTiling
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_TorusOrbit

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory Set
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

variable (K : Type) [Field K] [NumberField K]

private theorem unitScale_of_mem_torsion {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) : unitScale K ζ = 1 := by
  funext w
  show (w ((ζ : 𝓞 K) : K)) ^ 2 = 1
  rw [show w ((ζ : 𝓞 K) : K) = 1 from (mem_torsion K).mp hζ w, one_pow]

private theorem unitTorus_of_mem_torsion {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) (t : realSpace K) :
    unitTorus K ζ t = t := by
  show unitScale K ζ * t = t
  rw [unitScale_of_mem_torsion K hζ, one_mul]

private theorem unitTorus_torsion_mul {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) (u : (𝓞 K)ˣ) (t : realSpace K) :
    unitTorus K (ζ * u) t = unitTorus K u t := by
  rw [unitTorus_mul, unitTorus_of_mem_torsion K hζ]

private def unitsEquiv : torsion K × (Fin (rank K) → ℤ) ≃ (𝓞 K)ˣ :=
  Equiv.ofBijective (fun p => (p.1 : (𝓞 K)ˣ) * unitPow K p.2) (by
    constructor
    · intro p q h
      obtain ⟨r, -, huniq⟩ := exist_unique_eq_mul_prod K ((p.1 : (𝓞 K)ˣ) * unitPow K p.2)
      have hp : p = r := huniq p rfl
      have hq : q = r := huniq q (by rw [show ((p.1 : (𝓞 K)ˣ) * unitPow K p.2) = q.1 * unitPow K q.2 from h]; rfl)
      exact hp.trans hq.symm
    · intro u
      obtain ⟨r, hr, -⟩ := exist_unique_eq_mul_prod K u
      exact ⟨r, hr.symm⟩)

private theorem unitsEquiv_apply (p : torsion K × (Fin (rank K) → ℤ)) :
    unitsEquiv K p = (p.1 : (𝓞 K)ˣ) * unitPow K p.2 := rfl

private theorem unitTorus_unitsEquiv (p : torsion K × (Fin (rank K) → ℤ)) (t : realSpace K) :
    unitTorus K (unitsEquiv K p) t = unitTorus K (unitPow K p.2) t := by
  rw [unitsEquiv_apply, unitTorus_torsion_mul K p.1.2]

private theorem hasSum_prod_of_fintype {α β E : Type*} [Finite α] [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] {F : β → E} {S : E} (hF : HasSum F S) :
    HasSum (fun p : α × β => F p.2) (Nat.card α • S) := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  have key : (fun p : α × β => F p.2) = fun p => ∑ a : α, (if p.1 = a then F p.2 else 0) := by
    funext p; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [key, ← Finset.card_univ, ← Finset.sum_const]
  refine hasSum_sum fun a _ => ?_
  have hinj : Function.Injective (fun b : β => (a, b)) := fun b b' hbb' => (Prod.mk.inj hbb').2
  refine (hinj.hasSum_iff ?_).mp ?_
  · rintro ⟨a', b⟩ hnot
    rw [if_neg]
    rintro rfl
    exact hnot ⟨b, rfl⟩
  · convert hF using 1
    funext b
    exact if_pos rfl

private theorem hasSum_units_setIntegral_foldDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : realSpace K → E} (hh : IntegrableOn h (orthant K) (torusHaar K)) :
    HasSum (fun u : (𝓞 K)ˣ => ∫ t in foldDomain K, h (unitTorus K u t) ∂(torusHaar K))
      (torsionOrder K • ∫ t in orthant K, h t ∂(torusHaar K)) := by
  rw [← (unitsEquiv K).hasSum_iff]
  have hcomp : ((fun u : (𝓞 K)ˣ => ∫ t in foldDomain K, h (unitTorus K u t) ∂(torusHaar K)) ∘ (unitsEquiv K))
      = fun p => ∫ t in foldDomain K, h (unitTorus K (unitPow K p.2) t) ∂(torusHaar K) := by
    funext p
    simp only [Function.comp_apply, unitTorus_unitsEquiv]
  rw [hcomp, torsionOrder]
  exact hasSum_prod_of_fintype (hasSum_setIntegral_foldDomain K hh)

private theorem tsum_units_setIntegral_foldDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : realSpace K → E} (hh : IntegrableOn h (orthant K) (torusHaar K)) :
    ∑' u : (𝓞 K)ˣ, ∫ t in foldDomain K, h (unitTorus K u t) ∂(torusHaar K)
      = torsionOrder K • ∫ t in orthant K, h t ∂(torusHaar K) :=
  (hasSum_units_setIntegral_foldDomain K hh).tsum_eq

private theorem tsum_units_setIntegral_foldDomain_complex {h : realSpace K → ℂ}
    (hh : IntegrableOn h {t : realSpace K | ∀ w, 0 < t w} (torusHaar K)) :
    ∑' u : (𝓞 K)ˣ, ∫ t in foldDomain K, h (unitTorus K u t) ∂(torusHaar K)
      = (torsionOrder K : ℂ) * ∫ t in {t : realSpace K | ∀ w, 0 < t w}, h t ∂(torusHaar K) := by
  rw [tsum_units_setIntegral_foldDomain K hh, nsmul_eq_mul]
  rfl

private theorem tsum_units_setLIntegral_foldDomain (g : realSpace K → ℝ≥0∞) :
    ∑' u : (𝓞 K)ˣ, ∫⁻ t in foldDomain K, g (unitTorus K u t) ∂(torusHaar K)
      = torsionOrder K * ∫⁻ t in orthant K, g t ∂(torusHaar K) := by
  haveI : Fintype (torsion K) := Fintype.ofFinite _
  rw [← Equiv.tsum_eq (unitsEquiv K)]
  simp_rw [unitTorus_unitsEquiv]
  rw [ENNReal.tsum_prod', tsum_fintype]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, torsionOrder, Nat.card_eq_fintype_card, nsmul_eq_mul,
    setLIntegral_orthant_eq_tsum_foldDomain]

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_TorusOrbit
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_TorusGamma

open NumberField NumberField.InfinitePlace NumberField.Units MeasureTheory Set Filter
open NumberField.mixedEmbedding
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

variable (K : Type) [Field K] [NumberField K]

private def orbitExp (σ : ℝ) (w : InfinitePlace K) : ℝ := (mult w : ℝ) * (σ / 2)

omit [NumberField K] in
private theorem orbitExp_pos {σ : ℝ} (hσ : 0 < σ) (w : InfinitePlace K) : 0 < orbitExp K σ w := by
  unfold orbitExp
  have h2 : (0 : ℝ) < mult w := by exact_mod_cast (mult_pos (w := w))
  positivity

private theorem torusNorm_rpow_eq_prod {t : realSpace K} (ht : ∀ w, 0 < t w) (σ : ℝ) :
    torusNorm K t ^ (σ / 2) = ∏ w : InfinitePlace K, t w ^ orbitExp K σ w := by
  rw [torusNorm, ← Real.finsetProd_rpow _ _ (fun w _ => pow_nonneg (ht w).le _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (ht w).le, orbitExp]

private theorem torusDensity_lt_top (t : realSpace K) : (∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹) < ∞ :=
  ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top

private theorem measurableSet_setOf_pos : MeasurableSet {t : realSpace K | ∀ w, 0 < t w} :=
  measurableSet_orthant K

omit [NumberField K] in
private theorem setOf_pos_eq_pi :
    {t : realSpace K | ∀ w, 0 < t w} = Set.univ.pi fun _ : InfinitePlace K => Ioi (0 : ℝ) := by
  ext t
  simp

private theorem volume_restrict_setOf_pos :
    (volume : Measure (realSpace K)).restrict {t : realSpace K | ∀ w, 0 < t w}
      = Measure.pi fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Ioi 0) := by
  rw [setOf_pos_eq_pi, MeasureTheory.volume_pi, Measure.restrict_pi_pi]

private theorem measurable_torusForm_left (x : mixedSpace K) : Measurable fun t : realSpace K => torusForm K t x := by
  unfold torusForm
  exact Finset.measurable_sum _ fun w _ => ((measurable_pi_apply w).const_mul _).mul_const _

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_TorusGamma
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_ClassRegroup

p2m_open "NumberField Complex Filter Asymptotics Ideal NumberField.Ideal"
open FrobeniusDensity
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

variable (K : Type) [Field K] [NumberField K]

private theorem classZetaCoeff_eq_classCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) :
    classZetaCoeff K C n = Deep.Analytic.classCoeff K C n :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)

private theorem classZetaCoeff_zero (C : ClassGroup (𝓞 K)) : classZetaCoeff K C 0 = 0 := by
  rw [classZetaCoeff_eq_classCoeff]
  exact Deep.Analytic.classCoeff_zero K C

private theorem sum_classZetaCoeff_isBigO (C : ClassGroup (𝓞 K)) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖((classZetaCoeff K C k : ℂ))‖)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by

  have hT : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 0 n,
      (Deep.Analytic.classCoeff K C k : ℝ)) / (n : ℝ)) atTop
      (nhds (Deep.Analytic.heckeDensity K)) := by
    have h := (Deep.Analytic.tendsto_sum_classCoeff_div K C).comp
      tendsto_natCast_atTop_atTop (α := ℕ)
    simpa [Function.comp_def, Nat.floor_natCast] using h

  have hO1 : (fun n : ℕ => (∑ k ∈ Finset.Icc 0 n,
      (Deep.Analytic.classCoeff K C k : ℝ)) / (n : ℝ)) =O[atTop] (fun _ => (1 : ℝ)) :=
    hT.isBigO_one ℝ

  have hmul : (fun n : ℕ => ((∑ k ∈ Finset.Icc 0 n,
      (Deep.Analytic.classCoeff K C k : ℝ)) / (n : ℝ)) * (n : ℝ))
      =O[atTop] fun n : ℕ => (1 : ℝ) * (n : ℝ) := hO1.mul (isBigO_refl _ _)
  have hev : (fun n : ℕ => ((∑ k ∈ Finset.Icc 0 n,
      (Deep.Analytic.classCoeff K C k : ℝ)) / (n : ℝ)) * (n : ℝ))
      =ᶠ[atTop] fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, (Deep.Analytic.classCoeff K C k : ℝ) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp

  have hsum_eq : ∀ n : ℕ, (∑ k ∈ Finset.Icc 1 n, ‖((classZetaCoeff K C k : ℂ))‖)
      = ∑ k ∈ Finset.Icc 0 n, (Deep.Analytic.classCoeff K C k : ℝ) := by
    intro n
    have h01 : ∀ k ∈ Finset.Icc 1 n, ‖((classZetaCoeff K C k : ℂ))‖
        = (Deep.Analytic.classCoeff K C k : ℝ) := by
      intro k _
      rw [Complex.norm_natCast, classZetaCoeff_eq_classCoeff]
    rw [Finset.sum_congr rfl h01]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Deep.Analytic.classCoeff_zero]
    · have : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [this, Finset.sum_insert (by simp), Deep.Analytic.classCoeff_zero]
      simp
  calc (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖((classZetaCoeff K C k : ℂ))‖)
      = fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, (Deep.Analytic.classCoeff K C k : ℝ) :=
        funext hsum_eq
    _ =O[atTop] fun n : ℕ => (1 : ℝ) * (n : ℝ) := hmul.congr' hev EventuallyEq.rfl
    _ =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
        apply IsBigO.of_bound 1
        filter_upwards with n
        simp [Real.rpow_one]

private theorem lseriesSummable_classZetaCoeff (C : ClassGroup (𝓞 K)) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((classZetaCoeff K C n : ℂ))) s :=
  LSeriesSummable_of_sum_norm_bigO (sum_classZetaCoeff_isBigO K C) zero_le_one hs

private theorem class_cpow_fiber_tsum_norm (C : ClassGroup (𝓞 K)) (s : ℂ) (n : ℕ) :
    ∑' x : (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
        Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n},
      ‖((Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)‖
      = (classZetaCoeff K C n : ℝ) * ‖((n : ℂ)) ^ (-s)‖ := by
  classical
  have e : ((fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n}) ≃
      {I : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) = n} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  haveI : Finite ((fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n} : Set _) := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite ((fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n} : Set _)
  have hconst : ∀ x : ((fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n} : Set _),
      ‖((Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)‖ = ‖((n : ℂ)) ^ (-s)‖ := by
    intro x
    have hx : Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) = n := x.2
    rw [hx]
  rw [tsum_congr hconst, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [classZetaCoeff_eq_classCoeff, Deep.Analytic.classCoeff, ← Nat.card_eq_fintype_card]
  exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.card_congr e)

private theorem summable_class_cpow (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)) := by
  classical
  rw [← summable_norm_iff]
  set ν : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} → ℕ :=
    fun I => Ideal.absNorm (I.1 : Ideal (𝓞 K)) with hν
  rw [← (Equiv.sigmaFiberEquiv ν).summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨fun n => ?_, ?_⟩
  · haveI : Finite {x : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} // ν x = n} :=
      Finite.of_equiv _
        (show {I : (Ideal (𝓞 K))⁰ //
            ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) = n} ≃
            {x : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} // ν x = n} from
          { toFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
            invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
            left_inv := fun y => Subtype.ext rfl
            right_inv := fun x => Subtype.ext (Subtype.ext rfl) })
    haveI := Fintype.ofFinite {x : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} // ν x = n}
    exact (hasSum_fintype _).summable
  ·
    have hLS := (lseriesSummable_classZetaCoeff K C hs).norm
    refine hLS.congr fun n => ?_
    have key : ‖LSeries.term (fun n => ((classZetaCoeff K C n : ℂ))) s n‖
        = ∑' x : (ν ⁻¹' {n} : Set _),
          ‖((Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)‖ := by
      rw [class_cpow_fiber_tsum_norm K C s n]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [LSeries.term, classZetaCoeff_zero]
      · rw [LSeries.term_of_ne_zero (Nat.pos_iff_ne_zero.mp hn), norm_div,
          Complex.norm_natCast, Complex.cpow_neg, norm_inv, div_eq_mul_inv]
    exact key

private theorem summable_class_rpow (C : ClassGroup (𝓞 K)) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ)) ^ (-σ)) := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h := (summable_class_cpow K C hs).norm
  refine h.congr fun I => ?_
  have hN : 0 < Ideal.absNorm (I.1 : Ideal (𝓞 K)) :=
    Nat.pos_of_ne_zero (by
      intro h0
      exact absurd ((Ideal.absNorm_eq_zero_iff).mp h0)
        (mem_nonZeroDivisors_iff_ne_zero.mp I.1.2))
  rw [show ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) =
      (((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ)) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN)]
  simp

private theorem tsum_ofReal_ne_top_of_summable {α : Type} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a)
    (hf : Summable f) : ∑' a, ENNReal.ofReal (f a) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 hf]
  exact ENNReal.ofReal_ne_top

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

end TcFold_M4aTorus_ClassRegroup
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2"

section TcFold_M4aTorus_TorusUnfold

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
p2m_open "NumberField.InfinitePlace NumberField.Units MeasureTheory Set Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

variable (K : Type) [Field K] [NumberField K]

private scoped instance countable_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Countable (euclideanIdealLattice K I) :=
  Countable.of_equiv (mixedEmbedding.idealLattice K I)
    (ZLattice.comap_equiv ℝ (mixedEmbedding.idealLattice K I)
      (euclidean.toMixed K).toLinearEquiv).toEquiv

local notation3:max "Sub("J")" =>
    {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))}

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"
end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_TorusUnfold
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_TorusInversion

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
p2m_open "NumberField.InfinitePlace NumberField.Units MeasureTheory Set Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
open scoped nonZeroDivisors ENNReal Classical Real

variable (K : Type) [Field K] [NumberField K]

private theorem expMapBasis_neg (x : realSpace K) :
    expMapBasis (-x) = (expMapBasis x)⁻¹ := by
  have h : expMapBasis x * expMapBasis (-x) = 1 := by
    rw [← expMapBasis_add, add_neg_cancel, expMapBasis_zero]
  funext w
  have hw := congrFun h w
  rw [Pi.mul_apply, Pi.one_apply] at hw
  rw [Pi.inv_apply]
  exact eq_inv_of_mul_eq_one_right hw

omit [NumberField K] in

private theorem inv_mem_orthant {t : realSpace K} (ht : t ∈ orthant K) : t⁻¹ ∈ orthant K :=
  fun w => by rw [Pi.inv_apply]; exact inv_pos.mpr (ht w)

omit [NumberField K] in
private theorem measurable_inv_realSpace : Measurable (Inv.inv : realSpace K → realSpace K) :=
  measurable_pi_lambda _ fun w => (measurable_pi_apply w).inv

private theorem lintegral_comp_inv_torusHaar {g : realSpace K → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g t⁻¹ ∂(torusHaar K) = ∫⁻ t, g t ∂(torusHaar K) := by
  have hgi : Measurable fun t : realSpace K => g t⁻¹ := hg.comp (measurable_inv_realSpace K)
  rw [lintegral_torusHaar_eq K hgi, lintegral_torusHaar_eq K hg]
  congr 1
  simp_rw [← expMapBasis_neg]
  exact lintegral_neg_eq_self (fun x => g (expMapBasis x))

private theorem map_inv_torusHaar : (torusHaar K).map (Inv.inv : realSpace K → realSpace K) = torusHaar K := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_inv_realSpace K) hA, ← lintegral_indicator_one hA,
    ← lintegral_indicator_one ((measurable_inv_realSpace K) hA),
    ← lintegral_comp_inv_torusHaar K (measurable_one.indicator hA)]
  rfl

private theorem measurePreserving_inv_torusHaar :
    MeasurePreserving (Inv.inv : realSpace K → realSpace K) (torusHaar K) (torusHaar K) :=
  ⟨measurable_inv_realSpace K, map_inv_torusHaar K⟩

omit [NumberField K] in

private theorem place_unit_inv (w : InfinitePlace K) (u : (𝓞 K)ˣ) :
    w (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = (w (((u : (𝓞 K)ˣ) : 𝓞 K) : K))⁻¹ := by
  rw [← placeHom_apply K w u, ← placeHom_apply K w u⁻¹]
  exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])

private theorem unitTorus_inv (u : (𝓞 K)ˣ) (t : realSpace K) :
    (unitTorus K u t)⁻¹ = unitTorus K u⁻¹ t⁻¹ := by
  funext w
  rw [Pi.inv_apply, unitTorus_apply, unitTorus_apply, Pi.inv_apply, mul_inv, ← inv_pow,
    place_unit_inv]

section RefoldEngine

private noncomputable scoped instance instShiftVAdd : VAdd (Fin (rank K) → ℤ) (realSpace K) :=
  ⟨fun k x => shift K k + x⟩

private theorem shift_vadd_def (k : Fin (rank K) → ℤ) (x : realSpace K) :
    k +ᵥ x = shift K k + x := rfl

private noncomputable scoped instance instShiftAddAction : AddAction (Fin (rank K) → ℤ) (realSpace K) where
  zero_vadd x := by rw [shift_vadd_def, shift_zero, zero_add]
  add_vadd k k' x := by simp only [shift_vadd_def, shift_add, add_assoc]

private scoped instance instShiftMeasurableConstVAdd :
    MeasurableConstVAdd (Fin (rank K) → ℤ) (realSpace K) :=
  ⟨fun k => (measurable_const_add (shift K k))⟩

private scoped instance instShiftVAddInvariantMeasure :
    VAddInvariantMeasure (Fin (rank K) → ℤ) (realSpace K) volume :=
  ⟨fun k _ _ => measure_preimage_add volume (shift K k) _⟩

end RefoldEngine
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section RefoldBochner

private theorem unitPow_neg (k : Fin (rank K) → ℤ) : unitPow K (-k) = (unitPow K k)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← unitPow_add, add_neg_cancel, unitPow_zero])

private noncomputable scoped instance instTorusSMul :
    SMul (Multiplicative (Fin (rank K) → ℤ)) (realSpace K) :=
  ⟨fun k t => unitTorus K (unitPow K (Multiplicative.toAdd k)) t⟩

private theorem torus_smul_def (k : Multiplicative (Fin (rank K) → ℤ)) (t : realSpace K) :
    k • t = unitTorus K (unitPow K (Multiplicative.toAdd k)) t := rfl

private noncomputable scoped instance instTorusMulAction :
    MulAction (Multiplicative (Fin (rank K) → ℤ)) (realSpace K) where
  one_smul t := by rw [torus_smul_def, toAdd_one, unitPow_zero, unitTorus_one]
  mul_smul k k' t := by
    rw [torus_smul_def, torus_smul_def, torus_smul_def, toAdd_mul, unitPow_add, unitTorus_mul]

private scoped instance instTorusMeasurableConstSMul :
    MeasurableConstSMul (Multiplicative (Fin (rank K) → ℤ)) (realSpace K) :=
  ⟨fun k => measurable_unitTorus K (unitPow K (Multiplicative.toAdd k))⟩

private scoped instance instTorusSMulInvariantMeasure :
    SMulInvariantMeasure (Multiplicative (Fin (rank K) → ℤ)) (realSpace K) (torusHaar K) :=
  ⟨fun k _ hA => (measurePreserving_unitTorus K (unitPow K (Multiplicative.toAdd k))).measure_preimage
    hA.nullMeasurableSet⟩

private scoped instance instTorusCountable : Countable (Multiplicative (Fin (rank K) → ℤ)) :=
  inferInstanceAs (Countable (Fin (rank K) → ℤ))

private theorem isFundamentalDomain_foldDomain :
    IsFundamentalDomain (Multiplicative (Fin (rank K) → ℤ)) (foldDomain K) (torusHaar K) := by
  refine IsFundamentalDomain.mk'' (measurableSet_foldDomain K).nullMeasurableSet ?_ ?_ ?_
  · rw [← torusHaar_restrict_orthant K]
    filter_upwards [ae_restrict_mem (measurableSet_orthant K)] with t ht
    rw [← iUnion_foldPiece K, mem_iUnion] at ht
    obtain ⟨k, t₀, ht₀, heq⟩ := ht
    exact ⟨Multiplicative.ofAdd (-k), by
      rw [torus_smul_def, toAdd_ofAdd, ← heq, ← unitTorus_mul, ← unitPow_add,
        neg_add_cancel, unitPow_zero, unitTorus_one]; exact ht₀⟩
  · intro g hg
    refine Disjoint.aedisjoint ?_
    have hd := pairwise_disjoint_foldPiece K (i := Multiplicative.toAdd g) (j := 0)
      (by simpa using hg)
    rw [Function.onFun, show foldPiece K 0 = foldDomain K by
      rw [foldPiece, unitPow_zero]; exact Set.image_congr' (unitTorus_one K) |>.trans (image_id _)] at hd
    exact hd
  · exact fun g => (measurePreserving_unitTorus K _).quasiMeasurePreserving

private theorem isFundamentalDomain_inv_foldDomain :
    IsFundamentalDomain (Multiplicative (Fin (rank K) → ℤ))
      (Inv.inv '' foldDomain K) (torusHaar K) :=
  (isFundamentalDomain_foldDomain K).image_of_equiv (Equiv.inv (realSpace K))
    (measurePreserving_inv_torusHaar K).quasiMeasurePreserving
    (Equiv.inv (Multiplicative (Fin (rank K) → ℤ))) (fun g t => by
      show (unitTorus K (unitPow K (Multiplicative.toAdd g⁻¹)) t)⁻¹
        = unitTorus K (unitPow K (Multiplicative.toAdd g)) t⁻¹
      rw [toAdd_inv, unitPow_neg, unitTorus_inv, inv_inv])

end RefoldBochner
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

private theorem setIntegral_foldDomain_comp_inv_of_unitInvariant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : realSpace K → E} (hinv : ∀ u t, f (unitTorus K u t) = f t) :
    ∫ t in foldDomain K, f t⁻¹ ∂torusHaar K = ∫ t in foldDomain K, f t ∂torusHaar K := by
  rw [← (measurePreserving_inv_torusHaar K).setIntegral_image_emb
      (MeasurableEquiv.inv (realSpace K)).measurableEmbedding f (foldDomain K)]
  exact (isFundamentalDomain_inv_foldDomain K).setIntegral_eq (isFundamentalDomain_foldDomain K)
    (fun g t => by rw [torus_smul_def]; exact hinv _ _)

private theorem measurableSet_torusNorm_ge_one :
    MeasurableSet {t : realSpace K | 1 ≤ torusNorm K t} :=
  measurableSet_le measurable_const (continuous_torusNorm K).measurable

private theorem foldDomain_eq_union_halves :
    foldDomain K = (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t})
        ∪ (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t⁻¹}) := by
  ext t
  simp only [mem_union, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro ht
    rcases le_or_gt 1 (torusNorm K t) with h | h
    · exact Or.inl ⟨ht, h⟩
    · refine Or.inr ⟨ht, ?_⟩
      rw [torusNorm_inv, one_le_inv_iff₀]
      exact ⟨torusNorm_pos K (foldDomain_subset_orthant K ht), h.le⟩
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht

private theorem map_expMapBasis_smul_volume :
    Measure.map (expMapBasis : realSpace K → realSpace K)
      (foldConst K • (volume : Measure (realSpace K))) = torusHaar K := by
  ext A hA
  have hpre : MeasurableSet ((expMapBasis : realSpace K → realSpace K) ⁻¹' A) :=
    measurable_expMapBasis K hA
  rw [Measure.map_apply (measurable_expMapBasis K) hA, Measure.smul_apply, smul_eq_mul]
  calc foldConst K * volume ((expMapBasis : realSpace K → realSpace K) ⁻¹' A)
      = foldConst K * ∫⁻ _ in (expMapBasis : realSpace K → realSpace K) ⁻¹' A, (1 : ℝ≥0∞) := by
          rw [setLIntegral_one]
    _ = ∫⁻ _ in expMapBasis '' ((expMapBasis : realSpace K → realSpace K) ⁻¹' A),
          (1 : ℝ≥0∞) ∂(torusHaar K) :=
        (setLIntegral_image_expMapBasis_torusHaar' K hpre (g := fun _ => (1 : ℝ≥0∞))
          measurable_const).symm
    _ = torusHaar K (A ∩ orthant K) := by
          rw [setLIntegral_one, image_preimage_eq_inter_range, range_expMapBasis]
    _ = torusHaar K A := by
          rw [← Measure.restrict_apply hA, torusHaar_restrict_orthant]

private theorem setIntegral_image_expMapBasis_torusHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set (realSpace K)) (g : realSpace K → E) :
    ∫ t in expMapBasis '' s, g t ∂(torusHaar K) = (foldConst K).toReal • ∫ x in s, g (expMapBasis x) := by
  rw [← map_expMapBasis_smul_volume K, (measurableEmbedding_expMapBasis K).setIntegral_map,
    (injective_expMapBasis K).preimage_image, Measure.restrict_smul, integral_smul_measure]

private theorem torusHaar_torusNorm_eq_one :
    torusHaar K {t : realSpace K | torusNorm K t = 1} = 0 := by
  have hmeas : MeasurableSet {t : realSpace K | torusNorm K t = 1} :=
    (continuous_torusNorm K).measurable (measurableSet_singleton (1 : ℝ))
  rw [← map_expMapBasis_smul_volume K, Measure.map_apply (measurable_expMapBasis K) hmeas,
    Measure.smul_apply, smul_eq_mul]
  refine mul_eq_zero.mpr (Or.inr (measure_mono_null ?_ (Measure.addHaar_submodule volume
    (LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace K => ℝ)
      dirichletUnitTheorem.w₀)) ?_)))
  · intro x hx
    rw [mem_preimage, mem_setOf_eq, torusNorm_expMapBasis,
      ← Real.exp_nat_mul, Real.exp_eq_one_iff, mul_eq_zero] at hx
    simpa using hx.resolve_left (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
  · intro h
    have h1 : (fun _ => 1 : realSpace K) ∈ LinearMap.ker (LinearMap.proj (R := ℝ)
        (φ := fun _ : InfinitePlace K => ℝ) dirichletUnitTheorem.w₀) := h ▸ Submodule.mem_top
    simp at h1

private theorem aedisjoint_foldDomainHighHalves :
    AEDisjoint (torusHaar K) (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t})
      (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t⁻¹}) := by
  refine measure_mono_null ?_ (torusHaar_torusNorm_eq_one K)
  rintro t ⟨⟨ht, hge⟩, ht', hge'⟩
  rw [mem_setOf_eq, torusNorm_inv] at hge'
  have hN := torusNorm_pos K (foldDomain_subset_orthant K ht)
  exact le_antisymm ((one_le_inv_iff₀.mp hge').2) hge

private theorem mem_highHalf_inv_iff (t : realSpace K) :
    t⁻¹ ∈ {t' : realSpace K | 1 ≤ torusNorm K t'} ↔ t ∈ {t' | 1 ≤ torusNorm K t'⁻¹} := by
  simp only [mem_setOf_eq, torusNorm_inv]

private theorem unitTorus_mem_highHalf_iff (u : (𝓞 K)ˣ) (t : realSpace K) :
    unitTorus K u t ∈ {t' : realSpace K | 1 ≤ torusNorm K t'} ↔
      t ∈ {t' : realSpace K | 1 ≤ torusNorm K t'} := by
  simp only [mem_setOf_eq, torusNorm_unitTorus]

private theorem setIntegral_foldDomainLowHalf_eq_highHalf_comp_inv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : realSpace K → E} (hinv : ∀ u t, f (unitTorus K u t) = f t) :
    ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t⁻¹}, f t ∂torusHaar K
      = ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, f t⁻¹ ∂torusHaar K := by
  have hN1 : MeasurableSet {t' : realSpace K | 1 ≤ torusNorm K t'} :=
    measurableSet_torusNorm_ge_one K
  have hN1' : MeasurableSet {t' : realSpace K | 1 ≤ torusNorm K t'⁻¹} :=
    hN1.preimage (measurable_inv_realSpace K)

  rw [inter_comm (foldDomain K), inter_comm (foldDomain K),
    ← Measure.restrict_restrict hN1, ← Measure.restrict_restrict hN1',
    ← integral_indicator hN1', ← integral_indicator hN1]

  have key := setIntegral_foldDomain_comp_inv_of_unitInvariant K (E := E)
    (f := fun t => ({t' : realSpace K | 1 ≤ torusNorm K t'}).indicator (fun t' => f t'⁻¹) t)
    (fun u t => by
      simp only [Set.indicator_apply, unitTorus_mem_highHalf_iff, unitTorus_inv, hinv])

  rw [show (fun t => ({t' : realSpace K | 1 ≤ torusNorm K t'}).indicator (fun t' => f t'⁻¹) t⁻¹)
      = fun t => ({t' : realSpace K | 1 ≤ torusNorm K t'⁻¹}).indicator f t by
    funext t
    simp only [Set.indicator_apply, mem_highHalf_inv_iff, inv_inv]] at key
  exact key

private theorem foldBox_inter_preimage_normGeOne :
    foldBox K ∩ expMapBasis ⁻¹' {t : realSpace K | 1 ≤ torusNorm K t}
      = Set.univ.pi fun w => if w = dirichletUnitTheorem.w₀ then Set.Ici (0 : ℝ)
          else Set.Ico 0 2 := by
  ext x
  simp only [foldBox, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_univ_pi]
  rw [torusNorm_expMapBasis, one_le_pow_iff_of_nonneg (Real.exp_nonneg _) Module.finrank_pos.ne',
    Real.one_le_exp_iff]
  constructor
  · rintro ⟨hbox, h0⟩ w
    by_cases hw : w = dirichletUnitTheorem.w₀
    · subst hw; simpa using h0
    · simpa [hw] using hbox w hw
  · intro h
    refine ⟨fun w hw => by simpa [hw] using h w, by simpa using h dirichletUnitTheorem.w₀⟩

private theorem foldDomainHighHalf_eq_image :
    foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}
      = (expMapBasis : realSpace K → realSpace K) '' (Set.univ.pi fun w =>
          if w = dirichletUnitTheorem.w₀ then Set.Ici (0 : ℝ) else Set.Ico 0 2) := by
  rw [foldDomain, ← Set.image_inter_preimage, foldBox_inter_preimage_normGeOne]

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_TorusInversion
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_RayFoldInv

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

p2m_open "NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset {w : InfinitePlace K // IsReal w})

private def raySWeight (t : realSpace K) : ℂ := ∏ v ∈ S, ((Real.sqrt (t v) : ℝ) : ℂ)

private def rayMellinWeight (s : ℂ) (t : realSpace K) : ℂ :=
  ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) * raySWeight K S t

private theorem raySWeight_unitTorus (u : (𝓞 K)ˣ) (t : realSpace K) :
    raySWeight K S (unitTorus K u t)
      = (∏ v ∈ S, (((v : InfinitePlace K) ((u : 𝓞 K) : K) : ℝ) : ℂ)) * raySWeight K S t := by
  unfold raySWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hnn : (0 : ℝ) ≤ (v : InfinitePlace K) ((u : 𝓞 K) : K) := by positivity
  rw [unitTorus_apply, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnn, ofReal_mul]

private theorem rayMellinWeight_unitTorus (s : ℂ) (u : (𝓞 K)ˣ) (t : realSpace K) :
    rayMellinWeight K S s (unitTorus K u t)
      = (∏ v ∈ S, (((v : InfinitePlace K) ((u : 𝓞 K) : K) : ℝ) : ℂ)) * rayMellinWeight K S s t := by
  rw [rayMellinWeight, rayMellinWeight, torusNorm_unitTorus, raySWeight_unitTorus K S u t]
  ring

omit [NumberField K] in

private theorem prod_embedding_unit_mul (u : (𝓞 K)ˣ) (x : K) :
    (∏ v ∈ S, ((embedding_of_isReal v.2 (((u : 𝓞 K) : K) * x) : ℝ) : ℂ))
      = (∏ v ∈ S, ((embedding_of_isReal v.2 ((u : 𝓞 K) : K) : ℝ) : ℂ))
        * (∏ v ∈ S, ((embedding_of_isReal v.2 x : ℝ) : ℂ)) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => by rw [map_mul, ofReal_mul]

omit [NumberField K] in

private theorem signAt_mul_prod_embedding_eq_prod_place (u : (𝓞 K)ˣ) :
    signAt K S ((u : 𝓞 K) : K)
        * (∏ v ∈ S, ((embedding_of_isReal v.2 ((u : 𝓞 K) : K) : ℝ) : ℂ))
      = (∏ v ∈ S, (((v : InfinitePlace K) ((u : 𝓞 K) : K) : ℝ) : ℂ)) := by
  have hcast : ∀ s : SignType, ((s : ℤ) : ℂ) = ((s : ℝ) : ℂ) := fun s => by
    rcases s with _ | _ | _ <;> simp
  unfold signAt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← norm_embedding_of_isReal v.2, Real.norm_eq_abs,
    ← sign_mul_self (embedding_of_isReal v.2 ((u : 𝓞 K) : K)), ofReal_mul, hcast]

variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem uWeight_mul_prod_embedding_unit_smul (u : (𝓞 K)ˣ) (x : K) :
    uWeight K 𝔣 χ S 𝔞 (((u : 𝓞 K) : K) * x)
        * (∏ v ∈ S, ((embedding_of_isReal v.2 (((u : 𝓞 K) : K) * x) : ℝ) : ℂ))
      = (∏ v ∈ S, (((v : InfinitePlace K) ((u : 𝓞 K) : K) : ℝ) : ℂ))
          * (uWeight K 𝔣 χ S 𝔞 x * (∏ v ∈ S, ((embedding_of_isReal v.2 x : ℝ) : ℂ))) := by
  rw [uWeight_unit_smul K 𝔣 χ S 𝔞 u x, prod_embedding_unit_mul K S u x,
    ← signAt_mul_prod_embedding_eq_prod_place K S u]
  ring

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_RayFoldInv
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_RayFoldIntegrand

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

p2m_open "NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
open scoped nonZeroDivisors Classical Real

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem unit_mul_mem_fracIdeal (u : (𝓞 K)ˣ) {x : K}
    (hx : x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    ((u : 𝓞 K) : K) * x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h := Submodule.smul_mem ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) (u : 𝓞 K) hx
  rwa [Algebra.smul_def] at h

private def unitMulFracIdealEquiv (u : (𝓞 K)ˣ) :
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≃ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) where
  toFun x := ⟨((u : 𝓞 K) : K) * (x : K), unit_mul_mem_fracIdeal K 𝔞 u x.2⟩
  invFun x := ⟨(((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (x : K), unit_mul_mem_fracIdeal K 𝔞 u⁻¹ x.2⟩
  left_inv x := Subtype.ext (by
    simp only [← mul_assoc]
    rw [show (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * ((u : 𝓞 K) : K) = 1 by
      rw [← map_mul, Units.inv_mul, map_one], one_mul])
  right_inv x := Subtype.ext (by
    simp only [← mul_assoc]
    rw [show ((u : 𝓞 K) : K) * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 by
      rw [← map_mul, Units.mul_inv, map_one], one_mul])

private theorem unitMulFracIdealEquiv_apply (u : (𝓞 K)ˣ) (x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    ((unitMulFracIdealEquiv K 𝔞 u x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K)
      = ((u : 𝓞 K) : K) * (x : K) := rfl

private theorem torusForm_mixedEmbedding_unit_mul (u : (𝓞 K)ˣ) (t : realSpace K) (x : K) :
    torusForm K t (mixedEmbedding K (((u : 𝓞 K) : K) * x))
      = torusForm K (unitTorus K u t) (mixedEmbedding K x) := by
  rw [map_mul, ← unitSMul_smul, torusForm_unitSMul]

private def rayFoldSummand (c : ℝ) (t : realSpace K) (x : K) : ℂ :=
  uWeight K 𝔣 χ S 𝔞 x
    * (∏ v ∈ S, ((embedding_of_isReal v.2 x : ℝ) : ℂ))
    * ((Real.exp (-π * c * torusForm K t (mixedEmbedding K x)) : ℝ) : ℂ)

private theorem rayFoldSummand_unit_mul (c : ℝ) (u : (𝓞 K)ˣ) (t : realSpace K) (x : K) :
    rayFoldSummand K 𝔣 χ S 𝔞 c t (((u : 𝓞 K) : K) * x)
      = (∏ v ∈ S, (((v : InfinitePlace K) ((u : 𝓞 K) : K) : ℝ) : ℂ))
          * rayFoldSummand K 𝔣 χ S 𝔞 c (unitTorus K u t) x := by
  unfold rayFoldSummand
  rw [uWeight_mul_prod_embedding_unit_smul K S 𝔣 χ 𝔞 u x,
    torusForm_mixedEmbedding_unit_mul K u t x]
  ring

private def rayFoldMellinIntegrand (c : ℝ) (s : ℂ) (t : realSpace K) : ℂ :=
  (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
    * rayMellinWeight K S s t

private theorem rayFoldMellinIntegrand_unitInvariant (c : ℝ) (s : ℂ) (u : (𝓞 K)ˣ) (t : realSpace K) :
    rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s (unitTorus K u t)
      = rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t := by
  unfold rayFoldMellinIntegrand
  rw [rayMellinWeight_unitTorus K S s u t]
  have key : (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
      = (∏ v ∈ S, (((v : InfinitePlace K) ((u : 𝓞 K) : K) : ℝ) : ℂ))
          * ∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
              rayFoldSummand K 𝔣 χ S 𝔞 c (unitTorus K u t) (x : K) := by
    rw [← tsum_mul_left]
    exact ((unitMulFracIdealEquiv K 𝔞 u).tsum_eq
        (fun x => rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))).symm.trans
      (tsum_congr fun y => by
        rw [unitMulFracIdealEquiv_apply, rayFoldSummand_unit_mul K 𝔣 χ S 𝔞 c u t])
  rw [key]
  ring

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_RayFoldIntegrand
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_RayFoldSplit

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
p2m_open "MeasureTheory Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
open scoped nonZeroDivisors Classical Real

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})

private def rayFoldMellin (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℝ) (s : ℂ) : ℂ :=
  ∫ t in foldDomain K, rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t ∂(torusHaar K)

private def rayFoldMellinHigh (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℝ) (s : ℂ) : ℂ :=
  ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
    rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t ∂(torusHaar K)

private theorem rayFoldMellin_split_of_inv (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℝ) (s : ℂ)
    (D : realSpace K → ℂ) (P : ℂ) (pol : realSpace K → ℂ)
    (hInt : IntegrableOn (rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s)
      (foldDomain K) (torusHaar K))
    (hIntD : IntegrableOn D (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K))
    (hIntP : IntegrableOn pol (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K))
    (hinv : ∀ t ∈ orthant K, rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t⁻¹
        = D t + P * pol t) :
    rayFoldMellin K 𝔣 χ S 𝔞 c s
      = rayFoldMellinHigh K 𝔣 χ S 𝔞 c s
        + (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, D t ∂(torusHaar K))
        + P * (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, pol t ∂(torusHaar K)) := by
  have hN1 := measurableSet_torusNorm_ge_one K
  have hN1' : MeasurableSet {t : realSpace K | 1 ≤ torusNorm K t⁻¹} :=
    hN1.preimage (measurable_inv_realSpace K)
  have hHigh : MeasurableSet (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}) :=
    (measurableSet_foldDomain K).inter hN1
  have hIntPP : IntegrableOn (fun t => P * pol t)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := hIntP.const_mul P
  unfold rayFoldMellin rayFoldMellinHigh
  conv_lhs => rw [foldDomain_eq_union_halves K]
  rw [setIntegral_union₀ (aedisjoint_foldDomainHighHalves K)
      ((measurableSet_foldDomain K).inter hN1').nullMeasurableSet
      (hInt.mono_set Set.inter_subset_left) (hInt.mono_set Set.inter_subset_left),
    setIntegral_foldDomainLowHalf_eq_highHalf_comp_inv K
      (rayFoldMellinIntegrand_unitInvariant K 𝔣 χ S 𝔞 c s),
    setIntegral_congr_fun hHigh (fun t ht => hinv t (foldDomain_subset_orthant K ht.1)),
    integral_add hIntD hIntPP, integral_const_mul]
  ring

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_RayFoldSplit
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_HighHalf

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open MeasureTheory Set Filter
open scoped nonZeroDivisors ENNReal Classical Real

variable (K : Type) [Field K] [NumberField K]

private def highBox : Set (realSpace K) :=
  Set.univ.pi fun w => if w = w₀ then Set.Ici (0 : ℝ) else Set.Ico 0 2

private theorem measurableSet_highBox : MeasurableSet (highBox K) := by
  refine MeasurableSet.univ_pi fun w => ?_
  by_cases hw : w = w₀
  · rw [if_pos hw]; exact measurableSet_Ici
  · rw [if_neg hw]; exact measurableSet_Ico

private theorem highHalf_eq_image :
    foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}
      = (expMapBasis : realSpace K → realSpace K) '' highBox K :=
  foldDomainHighHalf_eq_image K

private theorem measurableSet_highHalf :
    MeasurableSet (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}) :=
  (measurableSet_foldDomain K).inter (measurableSet_torusNorm_ge_one K)

private theorem torusNorm_pos_of_mem_highHalf {t : realSpace K}
    (ht : t ∈ foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}) : 0 < torusNorm K t :=
  one_pos.trans_le ht.2

private theorem setLIntegral_highHalf_radial {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t in foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}, G (torusNorm K t) ∂(torusHaar K)
      = foldConst K * (2 ^ rank K
          * ∫⁻ u in Set.Ici (0 : ℝ), G (Real.exp u ^ Module.finrank ℚ K)) := by
  rw [highHalf_eq_image, setLIntegral_image_expMapBasis_torusHaar' K (measurableSet_highBox K)
    (g := fun t => G (torusNorm K t)) (hG.comp (measurable_torusNorm K))]
  congr 1
  simp_rw [torusNorm_expMapBasis]
  have hmeas : Measurable fun x : realSpace K => G (Real.exp (x w₀) ^ Module.finrank ℚ K) :=
    hG.comp (by fun_prop)
  rw [highBox, volume_pi, Measure.restrict_pi_pi, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' _ hmeas (Finset.mem_univ w₀), if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, Measure.pi_univ, if_neg
    (Finset.ne_of_mem_erase (Subtype.prop _)), Measure.restrict_apply_univ, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_ofNat, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [mul_comm]
  rfl

private theorem lintegral_Ici_ofReal_exp_mul_lt_top {a : ℝ} (ha : a < 0) :
    ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp (a * u)) < ∞ :=
  ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi ha 0)).lintegral_lt_top

private theorem integrableOn_highHalf_torusNorm_cpow_of_re_neg {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun t => ((torusNorm K t : ℝ) : ℂ) ^ z)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := by
  have hmeas : Measurable fun t : realSpace K => ((torusNorm K t : ℝ) : ℂ) ^ z :=
    (Complex.measurable_ofReal.comp (measurable_torusNorm K)).pow_const z
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have hG : Measurable fun r : ℝ => ENNReal.ofReal (r ^ z.re) :=
    (measurable_id.pow_const z.re).ennreal_ofReal
  unfold HasFiniteIntegral
  calc ∫⁻ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ‖((torusNorm K t : ℝ) : ℂ) ^ z‖ₑ
          ∂(torusHaar K)
      = ∫⁻ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
          ENNReal.ofReal ((torusNorm K t) ^ z.re) ∂(torusHaar K) := by
        refine setLIntegral_congr_fun (measurableSet_highHalf K) fun t ht => ?_
        rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos (torusNorm_pos_of_mem_highHalf K ht)]
    _ = foldConst K * (2 ^ rank K
          * ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal ((Real.exp u ^ Module.finrank ℚ K) ^ z.re)) :=
        setLIntegral_highHalf_radial K hG
    _ = foldConst K * (2 ^ rank K
          * ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp ((Module.finrank ℚ K * z.re) * u))) := by
        congr 2
        refine lintegral_congr fun u => ?_
        rw [← Real.exp_nat_mul, ← Real.exp_mul,
          show (Module.finrank ℚ K : ℝ) * u * z.re = Module.finrank ℚ K * z.re * u by ring]
    _ < ∞ := ENNReal.mul_lt_top (foldConst_ne_top K).lt_top
          (ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top).lt_top
            (lintegral_Ici_ofReal_exp_mul_lt_top (mul_neg_of_pos_of_neg hn hz)))

private def polarVolume : ℂ :=
  (((foldConst K).toReal * 2 ^ rank K / Module.finrank ℚ K : ℝ) : ℂ)

private theorem integral_Ici_exp_pow_cpow_neg {z : ℂ} (hz : 0 < z.re) :
    ∫ u in Set.Ici (0 : ℝ), (((Real.exp u ^ Module.finrank ℚ K : ℝ)) : ℂ) ^ (-z)
      = 1 / ((Module.finrank ℚ K : ℂ) * z) := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have ha : (-((Module.finrank ℚ K : ℂ) * z)).re < 0 := by
    have : ((Module.finrank ℚ K : ℂ) * z).re = (Module.finrank ℚ K : ℝ) * z.re := by
      simp [Complex.mul_re]
    rw [Complex.neg_re, this, neg_lt_zero]
    positivity
  have hfun : ∀ u : ℝ, (((Real.exp u ^ Module.finrank ℚ K : ℝ)) : ℂ) ^ (-z)
      = Complex.exp (-((Module.finrank ℚ K : ℂ) * z) * u) := by
    intro u
    rw [← Real.exp_nat_mul, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    push_cast
    ring_nf
  rw [setIntegral_congr_set (Ioi_ae_eq_Ici : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici 0).symm]
  simp_rw [hfun]
  rw [integral_exp_mul_complex_Ioi ha 0]
  simp [neg_div_neg_eq]

private theorem setIntegral_highHalf_torusNorm_cpow_neg {z : ℂ} (hz : 0 < z.re) :
    ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z) ∂(torusHaar K)
      = polarVolume K / z := by
  have hn0 : (Module.finrank ℚ K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [Complex.zero_re] at hz
    exact lt_irrefl _ hz
  have hrest : ∏ w ∈ (Finset.univ : Finset (InfinitePlace K)).erase w₀,
      (∫ u, (if w = w₀ then (((Real.exp u ^ Module.finrank ℚ K : ℝ)) : ℂ) ^ (-z) else (1 : ℂ))
        ∂(volume.restrict (if w = w₀ then Set.Ici (0 : ℝ) else Set.Ico 0 2)))
      = 2 ^ rank K := by
    rw [Finset.prod_congr rfl (g := fun _ => (2 : ℂ)), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ w₀), Finset.card_univ]
    · rfl
    · intro w hw
      have hw' : w ≠ w₀ := Finset.ne_of_mem_erase hw
      simp only [if_neg hw']
      rw [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ico_of_le zero_le_two,
        sub_zero, Complex.real_smul, mul_one, Complex.ofReal_ofNat]
  have hbox : ∫ x in highBox K, (((Real.exp (x w₀) ^ Module.finrank ℚ K : ℝ)) : ℂ) ^ (-z)
      = 2 ^ rank K * (1 / ((Module.finrank ℚ K : ℂ) * z)) := by
    have hf : (fun x : realSpace K => (((Real.exp (x w₀) ^ Module.finrank ℚ K : ℝ)) : ℂ) ^ (-z))
        = fun x => ∏ w, (fun (w : InfinitePlace K) (u : ℝ) =>
            if w = w₀ then (((Real.exp u ^ Module.finrank ℚ K : ℝ)) : ℂ) ^ (-z) else (1 : ℂ))
              w (x w) := by
      funext x
      simp only []
      rw [Finset.prod_ite_eq' (Finset.univ : Finset (InfinitePlace K)) w₀, if_pos (Finset.mem_univ _)]
    rw [hf, highBox, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
      (f := fun (w : InfinitePlace K) (u : ℝ) =>
        if w = w₀ then (((Real.exp u ^ Module.finrank ℚ K : ℝ)) : ℂ) ^ (-z) else (1 : ℂ))
      (μ := fun w => volume.restrict (if w = w₀ then Set.Ici (0 : ℝ) else Set.Ico 0 2)),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
    simp only [if_true]
    rw [integral_Ici_exp_pow_cpow_neg K hz, hrest, mul_comm]
  rw [highHalf_eq_image, setIntegral_image_expMapBasis_torusHaar]
  simp_rw [torusNorm_expMapBasis]
  rw [hbox, polarVolume, Complex.real_smul]
  push_cast
  field_simp

private theorem neg_mul_exp_add_mul_le {γ b : ℝ} (hγ : 0 < γ) (hb : 0 < b) (u : ℝ) :
    -γ * Real.exp u + b * u ≤ b * Real.log (b / γ) - b := by
  have hb0 : b ≠ 0 := hb.ne'
  have hγ0 : γ ≠ 0 := hγ.ne'
  have h1 : (u - Real.log (b / γ)) + 1 ≤ Real.exp (u - Real.log (b / γ)) := Real.add_one_le_exp _
  have h2 : Real.exp (u - Real.log (b / γ)) = Real.exp u * (γ / b) := by
    rw [Real.exp_sub, Real.exp_log (by positivity)]
    field_simp
  rw [h2] at h1
  have h3 : b * ((u - Real.log (b / γ)) + 1) ≤ γ * Real.exp u := by
    calc b * ((u - Real.log (b / γ)) + 1) ≤ b * (Real.exp u * (γ / b)) :=
          mul_le_mul_of_nonneg_left h1 hb.le
      _ = γ * Real.exp u := by field_simp
  linarith

private theorem lintegral_Ici_radialMajorant_lt_top (C : ℝ) {γ : ℝ} (hγ : 0 < γ) (b : ℝ) :
    ∫⁻ u in Set.Ici (0 : ℝ),
        ENNReal.ofReal (C * Real.exp (-γ * Real.exp u) * Real.exp (b * u)) < ∞ := by
  set b' : ℝ := max (b + 1) 1 with hb'
  have hb'pos : 0 < b' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbb' : b ≤ b' - 1 := by linarith [le_max_left (b + 1) 1]
  set C₀ : ℝ := b' * Real.log (b' / γ) - b' with hC₀
  have key : ∀ u : ℝ, 0 ≤ u → C * Real.exp (-γ * Real.exp u) * Real.exp (b * u)
      ≤ |C| * Real.exp C₀ * Real.exp (-1 * u) := by
    intro u hu
    have hC : C * Real.exp (-γ * Real.exp u) * Real.exp (b * u)
        ≤ |C| * (Real.exp (-γ * Real.exp u) * Real.exp (b * u)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    refine hC.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h := neg_mul_exp_add_mul_le hγ hb'pos u
    have hbu : b * u ≤ (b' - 1) * u := mul_le_mul_of_nonneg_right hbb' hu
    linarith
  calc ∫⁻ u in Set.Ici (0 : ℝ),
          ENNReal.ofReal (C * Real.exp (-γ * Real.exp u) * Real.exp (b * u))
      ≤ ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal (|C| * Real.exp C₀ * Real.exp (-1 * u)) :=
        setLIntegral_mono' measurableSet_Ici fun u hu => ENNReal.ofReal_le_ofReal (key u hu)
    _ = ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal (|C| * Real.exp C₀)
          * ENNReal.ofReal (Real.exp (-1 * u)) := by
        refine lintegral_congr fun u => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (|C| * Real.exp C₀)
          * ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-1 * u)) :=
        lintegral_const_mul _ (by fun_prop)
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_Ici_ofReal_exp_mul_lt_top (by norm_num))

private theorem integrableOn_highHalf_radialMajorant (C : ℝ) {γ : ℝ} (hγ : 0 < γ) (a : ℝ) :
    IntegrableOn (fun t => C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
        * (torusNorm K t) ^ a)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := by
  have hN := measurable_torusNorm K
  have hmeas : Measurable fun t : realSpace K =>
      C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹) * (torusNorm K t) ^ a :=
    (measurable_const.mul ((measurable_const.mul (hN.pow_const _)).exp)).mul (hN.pow_const _)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have hG : Measurable fun r : ℝ =>
      ENNReal.ofReal (|C| * Real.exp (-γ * r ^ (Module.finrank ℚ K : ℝ)⁻¹) * r ^ a) :=
    ((measurable_const.mul ((measurable_const.mul (measurable_id.pow_const _)).exp)).mul
      (measurable_id.pow_const _)).ennreal_ofReal
  unfold HasFiniteIntegral
  calc ∫⁻ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
          ‖C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹) * (torusNorm K t) ^ a‖ₑ
          ∂(torusHaar K)
      ≤ ∫⁻ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ENNReal.ofReal
          (|C| * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹) * (torusNorm K t) ^ a)
          ∂(torusHaar K) := by
        refine setLIntegral_mono' (measurableSet_highHalf K) fun t ht => ?_
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.exp_nonneg _),
          abs_of_nonneg (Real.rpow_nonneg (torusNorm_pos_of_mem_highHalf K ht).le _)]
    _ = foldConst K * (2 ^ rank K * ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal
          (|C| * Real.exp (-γ * ((Real.exp u ^ Module.finrank ℚ K) ^ (Module.finrank ℚ K : ℝ)⁻¹))
            * (Real.exp u ^ Module.finrank ℚ K) ^ a)) :=
        setLIntegral_highHalf_radial K hG
    _ = foldConst K * (2 ^ rank K * ∫⁻ u in Set.Ici (0 : ℝ), ENNReal.ofReal
          (|C| * Real.exp (-γ * Real.exp u) * Real.exp ((Module.finrank ℚ K * a) * u))) := by
        congr 2
        refine lintegral_congr fun u => ?_
        rw [Real.pow_rpow_inv_natCast (Real.exp_nonneg _) Module.finrank_pos.ne',
          ← Real.exp_nat_mul, ← Real.exp_mul,
          show (Module.finrank ℚ K : ℝ) * u * a = Module.finrank ℚ K * a * u by ring]
    _ < ∞ := ENNReal.mul_lt_top (foldConst_ne_top K).lt_top
          (ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top).lt_top
            (lintegral_Ici_radialMajorant_lt_top |C| hγ _))

private theorem integrableOn_highHalf_of_norm_le {Φ : realSpace K → ℂ}
    (hΦ : AEStronglyMeasurable Φ
      ((torusHaar K).restrict (foldDomain K ∩ {t | 1 ≤ torusNorm K t})))
    (C : ℝ) {γ : ℝ} (hγ : 0 < γ) (a : ℝ)
    (hb : ∀ t ∈ foldDomain K ∩ {t | 1 ≤ torusNorm K t},
      ‖Φ t‖ ≤ C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
        * (torusNorm K t) ^ a) :
    IntegrableOn Φ (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) :=
  Integrable.mono' (integrableOn_highHalf_radialMajorant K C hγ a) hΦ
    (ae_restrict_of_forall_mem (measurableSet_highHalf K) hb)

private theorem norm_cpow_mul_log_le {N : ℝ} (hN : 1 ≤ N) {s : ℂ} {σ : ℝ} (hs : s.re ≤ σ) :
    ‖((N : ℂ) ^ (s / 2)) * Complex.log (N : ℂ) * (1 / 2)‖ ≤ N ^ (σ / 2 + 1) := by
  have hN0 : 0 < N := one_pos.trans_le hN
  have hlog : ‖Complex.log (N : ℂ)‖ = Real.log N := by
    rw [← Complex.ofReal_log hN0.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hN)]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN0, hlog, Complex.div_ofNat_re,
    Real.rpow_add hN0, Real.rpow_one]
  have h1 : N ^ (s.re / 2) ≤ N ^ (σ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h2 : Real.log N * ‖(1 / 2 : ℂ)‖ ≤ N := by
    have hl : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hhalf]
    nlinarith [Real.log_nonneg hN]
  calc N ^ (s.re / 2) * Real.log N * ‖(1 / 2 : ℂ)‖
      = N ^ (s.re / 2) * (Real.log N * ‖(1 / 2 : ℂ)‖) := by ring
    _ ≤ N ^ (σ / 2) * N :=
        mul_le_mul h1 h2 (mul_nonneg (Real.log_nonneg hN) (norm_nonneg _)) (Real.rpow_nonneg hN0.le _)

private theorem differentiable_setIntegral_highHalf_mul_cpow {Ψ : realSpace K → ℂ} (hΨ : Measurable Ψ)
    (C : ℝ) {γ : ℝ} (hγ : 0 < γ) (a : ℝ)
    (hb : ∀ t ∈ foldDomain K ∩ {t | 1 ≤ torusNorm K t},
      ‖Ψ t‖ ≤ C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
        * (torusNorm K t) ^ a) :
    Differentiable ℂ fun s : ℂ =>
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
        Ψ t * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) ∂(torusHaar K) := by
  intro s₀
  have hNm : Measurable fun t : realSpace K => ((torusNorm K t : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_torusNorm K)
  have hF_meas : ∀ s : ℂ, AEStronglyMeasurable
      (fun t : realSpace K => Ψ t * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2))
      ((torusHaar K).restrict (foldDomain K ∩ {t | 1 ≤ torusNorm K t})) :=
    fun s => (hΨ.mul (hNm.pow_const _)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun t : realSpace K => Ψ t * (((torusNorm K t : ℝ) : ℂ) ^ (s₀ / 2)
        * Complex.log ((torusNorm K t : ℝ) : ℂ) * (1 / 2)))
      ((torusHaar K).restrict (foldDomain K ∩ {t | 1 ≤ torusNorm K t})) :=
    (hΨ.mul (((hNm.pow_const _).mul (Complex.measurable_log.comp hNm)).mul
      measurable_const)).aestronglyMeasurable

  have hb' : ∀ t ∈ foldDomain K ∩ {t | 1 ≤ torusNorm K t},
      ‖Ψ t‖ ≤ |C| * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
        * (torusNorm K t) ^ a := fun t ht =>
    (hb t ht).trans (by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by
        have := torusNorm_pos_of_mem_highHalf K ht
        positivity))

  have hF_int : IntegrableOn (fun t : realSpace K => Ψ t * ((torusNorm K t : ℝ) : ℂ) ^ (s₀ / 2))
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := by
    refine integrableOn_highHalf_of_norm_le K (hF_meas s₀) |C| hγ (a + s₀.re / 2) fun t ht => ?_
    have hN0 := torusNorm_pos_of_mem_highHalf K ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN0, Complex.div_ofNat_re, Real.rpow_add hN0,
      ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hb' t ht) (Real.rpow_nonneg hN0.le _)

  have h_bound : ∀ᵐ t ∂((torusHaar K).restrict (foldDomain K ∩ {t | 1 ≤ torusNorm K t})),
      ∀ s ∈ Metric.ball s₀ 1,
        ‖Ψ t * (((torusNorm K t : ℝ) : ℂ) ^ (s / 2) * Complex.log ((torusNorm K t : ℝ) : ℂ)
          * (1 / 2))‖
        ≤ |C| * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
            * (torusNorm K t) ^ (a + ((s₀.re + 1) / 2 + 1)) := by
    refine ae_restrict_of_forall_mem (measurableSet_highHalf K) fun t ht s hs => ?_
    have hN0 := torusNorm_pos_of_mem_highHalf K ht
    have hN1 : 1 ≤ torusNorm K t := ht.2
    have hsre : s.re ≤ s₀.re + 1 := by
      have h1 : (s - s₀).re ≤ ‖s - s₀‖ := Complex.re_le_norm _
      have h2 : ‖s - s₀‖ < 1 := by rwa [← dist_eq_norm]
      rw [Complex.sub_re] at h1
      linarith
    rw [norm_mul, Real.rpow_add hN0 a, ← mul_assoc]
    exact mul_le_mul (hb' t ht) (norm_cpow_mul_log_le hN1 hsre) (norm_nonneg _) (by positivity)
  have bound_int := integrableOn_highHalf_radialMajorant K |C| hγ (a + ((s₀.re + 1) / 2 + 1))
  have h_diff : ∀ᵐ t ∂((torusHaar K).restrict (foldDomain K ∩ {t | 1 ≤ torusNorm K t})),
      ∀ s ∈ Metric.ball s₀ 1,
        HasDerivAt (fun s : ℂ => Ψ t * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2))
          (Ψ t * (((torusNorm K t : ℝ) : ℂ) ^ (s / 2) * Complex.log ((torusNorm K t : ℝ) : ℂ)
            * (1 / 2))) s := by
    refine ae_restrict_of_forall_mem (measurableSet_highHalf K) fun t ht s _ => ?_
    have hN0 : ((torusNorm K t : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (torusNorm_pos_of_mem_highHalf K ht).ne'
    have h := ((hasDerivAt_id s).div_const (2 : ℂ)).const_cpow (c := ((torusNorm K t : ℝ) : ℂ))
      (Or.inl hN0)
    simpa using h.const_mul (Ψ t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall hF_meas) hF_int hF'_meas h_bound bound_int h_diff).2.differentiableAt

private theorem torusForm_const (c : ℝ) (x : mixedSpace K) :
    torusForm K (fun _ => c) x = c * torusForm K (fun _ => (1 : ℝ)) x := by
  simp only [torusForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

private theorem exists_expMapBasis_lower :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ highBox K, ∀ w : InfinitePlace K,
      β * Real.exp (x w₀) ≤ expMapBasis x w := by
  let A : InfinitePlace K → {w : InfinitePlace K // w ≠ w₀} → ℝ :=
    fun w i => w (fundSystem K (equivFinRank.symm i))
  have hA : ∀ w i, 0 < A w i := fun w i => pos_at_place _ _
  let βw : InfinitePlace K → ℝ := fun w => ∏ i, min 1 (A w i ^ (2 : ℝ))
  have hβw : ∀ w, 0 < βw w := fun w =>
    Finset.prod_pos fun i _ => lt_min one_pos (Real.rpow_pos_of_pos (hA w i) _)
  obtain ⟨w₁, -, hw₁⟩ := Finset.exists_min_image Finset.univ βw Finset.univ_nonempty
  refine ⟨βw w₁, hβw w₁, fun x hx w => ?_⟩
  have hle : βw w ≤ ∏ i : {w : InfinitePlace K // w ≠ w₀}, A w i ^ x i.1 := by
    refine Finset.prod_le_prod (fun i _ => (lt_min one_pos (Real.rpow_pos_of_pos (hA w i) _)).le)
      fun i _ => ?_
    have hxi : x i.1 ∈ Set.Ico (0 : ℝ) 2 := by
      have h := (Set.mem_univ_pi.mp hx) i.1
      rw [if_neg i.2] at h
      exact h
    rcases le_or_gt 1 (A w i) with h1 | h1
    · exact (min_le_left _ _).trans (Real.one_le_rpow h1 hxi.1)
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_exponent_ge (hA w i) h1.le hxi.2.le)
  calc βw w₁ * Real.exp (x w₀) ≤ βw w * Real.exp (x w₀) :=
        mul_le_mul_of_nonneg_right (hw₁ w (Finset.mem_univ _)) (Real.exp_nonneg _)
    _ ≤ (∏ i : {w : InfinitePlace K // w ≠ w₀}, A w i ^ x i.1) * Real.exp (x w₀) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = expMapBasis x w := by
        rw [expMapBasis_apply', Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem exists_highHalf_coord_lower :
    ∃ β : ℝ, 0 < β ∧ ∀ t ∈ foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t},
      ∀ w : InfinitePlace K, β * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹ ≤ t w := by
  obtain ⟨β, hβ, h⟩ := exists_expMapBasis_lower K
  refine ⟨β, hβ, fun t ht w => ?_⟩
  rw [highHalf_eq_image] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [torusNorm_expMapBasis, Real.pow_rpow_inv_natCast (Real.exp_nonneg _) Module.finrank_pos.ne']
  exact h x hx w

private theorem exists_torusForm_highHalf_lower :
    ∃ β : ℝ, 0 < β ∧ ∀ t ∈ foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t},
      ∀ x : mixedSpace K, β * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹
        * torusForm K (fun _ => (1 : ℝ)) x ≤ torusForm K t x := by
  obtain ⟨β, hβ, h⟩ := exists_highHalf_coord_lower K
  refine ⟨β, hβ, fun t ht x => ?_⟩
  rw [← torusForm_const]
  exact torusForm_mono K (fun w => h t ht w) x

private theorem sum_le_torusForm (S : Finset {w : InfinitePlace K // IsReal w}) {t : realSpace K}
    (ht : ∀ w, 0 ≤ t w) (y : K) :
    ∑ v ∈ S, t v.1 * ((v.1 : InfinitePlace K) y) ^ 2 ≤ torusForm K t (mixedEmbedding K y) := by
  have h1 : ∑ v ∈ S, t v.1 * ((v.1 : InfinitePlace K) y) ^ 2
      ≤ ∑ v : {w : InfinitePlace K // IsReal w}, t v.1 * ((v.1 : InfinitePlace K) y) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun v => by have := ht v.1; positivity
  refine h1.trans ?_
  rw [torusForm, sum_eq_sum_add_sum]
  have h2 : ∀ w : InfinitePlace K,
      0 ≤ (mult w : ℝ) * t w * normAtPlace w (mixedEmbedding K y) ^ 2 := fun w => by
    have := ht w
    positivity
  calc ∑ v : {w : InfinitePlace K // IsReal w}, t v.1 * ((v.1 : InfinitePlace K) y) ^ 2
      = ∑ v : {w : InfinitePlace K // IsReal w},
          (mult v.1 : ℝ) * t v.1 * normAtPlace v.1 (mixedEmbedding K y) ^ 2 :=
        Finset.sum_congr rfl fun v _ => by rw [mult_isReal, normAtPlace_apply, Nat.cast_one, one_mul]
    _ ≤ _ := le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => h2 w.1)

private theorem norm_sq_le_torusForm_one (y : K) :
    ‖(euclidean.toMixed K).symm (mixedEmbedding K y)‖ ^ 2
      ≤ torusForm K (fun _ => (1 : ℝ)) (mixedEmbedding K y) := by
  set z := (euclidean.toMixed K).symm (mixedEmbedding K y) with hz
  have hy : mixedEmbedding K y = euclidean.toMixed K z := by
    rw [hz, ContinuousLinearEquiv.apply_symm_apply]
  rw [hy, torusForm_toMixed, torusFormCoord, M4aP2.norm_sq_eq_sum]
  simp only [one_mul, mul_one]
  refine add_le_add le_rfl (Finset.sum_le_sum fun w _ => ?_)
  nlinarith [Complex.normSq_nonneg (z.snd w)]

private theorem exists_pos_le_torusForm_one (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ q₀ : ℝ, 0 < q₀ ∧ ∀ y : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K), (y : K) ≠ 0 →
      q₀ ≤ torusForm K (fun _ => (1 : ℝ)) (mixedEmbedding K (y : K)) := by
  obtain ⟨m, hm, h⟩ := Deep.Analytic.exists_min_norm (Deep.Analytic.euclideanIdealLattice K 𝔟)
  refine ⟨m ^ 2, by positivity, fun y hy => ?_⟩
  have hv : M4aP2.idealPointEquiv K 𝔟 y ≠ 0 := by
    intro h0
    apply hy
    have h1 : ((M4aP2.idealPointEquiv K 𝔟 y : Deep.Analytic.euclideanIdealLattice K 𝔟) :
        euclidean.mixedSpace K) = 0 := by
      simp [h0]
    rw [M4aP2.idealPointEquiv_apply] at h1
    have h2 : mixedEmbedding K (y : K) = 0 := by
      have h3 := congrArg (euclidean.toMixed K) h1
      rwa [ContinuousLinearEquiv.apply_symm_apply, map_zero] at h3
    exact (map_eq_zero_iff _ (mixedEmbedding_injective K)).mp h2
  have h2 := h _ hv
  rw [M4aP2.idealPointEquiv_apply] at h2
  calc m ^ 2 ≤ ‖(euclidean.toMixed K).symm (mixedEmbedding K (y : K))‖ ^ 2 :=
        pow_le_pow_left₀ hm.le h2 2
    _ ≤ _ := norm_sq_le_torusForm_one K (y : K)

private theorem summable_exp_torusForm_one (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {κ' : ℝ} (hκ' : 0 < κ') :
    Summable fun y : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) =>
      Real.exp (-π * κ' * torusForm K (fun _ => (1 : ℝ)) (mixedEmbedding K (y : K))) := by
  have hL : Summable fun v : Deep.Analytic.euclideanIdealLattice K 𝔟 =>
      Real.exp (-π * κ' * ‖(v : euclidean.mixedSpace K)‖ ^ 2) :=
    Deep.Analytic.latticeThetaSummable (Deep.Analytic.euclideanIdealLattice K 𝔟) hκ'
  have h1 := (Equiv.summable_iff (M4aP2.idealPointEquiv K 𝔟)).mpr hL
  refine Summable.of_nonneg_of_le (fun y => Real.exp_nonneg _) (fun y => ?_) h1
  rw [Function.comp_apply, M4aP2.idealPointEquiv_apply]
  refine Real.exp_le_exp.mpr ?_
  have := norm_sq_le_torusForm_one K (y : K)
  nlinarith [mul_pos Real.pi_pos hκ']

private theorem sqrt_mul_mul_exp_neg_le {a r c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    Real.sqrt a * r * Real.exp (-(c * (a * r ^ 2))) ≤ 1 / Real.sqrt c := by
  set v := Real.sqrt c * (Real.sqrt a * r) with hv
  have hv2 : v ^ 2 = c * (a * r ^ 2) := by
    rw [hv, mul_pow, mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt ha]
  have key : v ≤ Real.exp (v ^ 2) := by
    have := Real.add_one_le_exp (v ^ 2)
    nlinarith [sq_nonneg (v - 1 / 2)]
  have hc' : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsr : Real.sqrt a * r = v / Real.sqrt c := by
    rw [hv]
    field_simp
  rw [← hv2, hsr, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc', Real.exp_neg,
    mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
  exact key

private theorem tail_bound_highHalf (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {κ : ℝ} (hκ : 0 < κ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (a : K → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ y : K, ‖a y‖ ≤ B * ∏ v ∈ S, (v.1 : InfinitePlace K) y) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t},
      ‖∑' y : {y : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) // (y : K) ≠ 0},
          a (y.1 : K) * ((Real.exp (-π * κ * torusForm K t (mixedEmbedding K (y.1 : K))) : ℝ) : ℂ)‖
        * ‖∏ v ∈ S, ((Real.sqrt (t v.1) : ℝ) : ℂ)‖
      ≤ C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨β, hβ, hQ⟩ := exists_torusForm_highHalf_lower K
  obtain ⟨q₀, hq₀, hq⟩ := exists_pos_le_torusForm_one K 𝔟
  set κ' : ℝ := κ / 2 with hκ'
  have hκ'0 : 0 < κ' := by positivity
  set γ : ℝ := π * κ' * β * q₀ with hγ
  have hπκ : 0 < π * κ' := mul_pos Real.pi_pos hκ'0
  have hγ0 : 0 < γ := by positivity
  set h : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) → ℝ := fun y =>
    Real.exp (-π * (κ' * β) * torusForm K (fun _ => (1 : ℝ)) (mixedEmbedding K (y : K))) with hh
  have hsum : Summable h := summable_exp_torusForm_one K 𝔟 (by positivity)
  have hsum' := hsum.subtype fun y : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) => (y : K) ≠ 0
  set T : ℝ := ∑' y : {y : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) // (y : K) ≠ 0}, h y.1 with hT
  set cS : ℝ := (1 / Real.sqrt (π * κ')) ^ S.card with hcS
  refine ⟨B * cS * Real.exp γ * T, γ, hγ0, fun t ht => ?_⟩
  have hN1 : 1 ≤ torusNorm K t := ht.2
  have htpos : ∀ w, 0 < t w := foldDomain_subset_orthant K ht.1
  set Nr : ℝ := (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹ with hNr
  have hNr1 : 1 ≤ Nr := Real.one_le_rpow hN1 (by positivity)
  set A : ℝ := B * cS * Real.exp γ * Real.exp (-γ * Nr) with hAdef

  have hW : ‖∏ v ∈ S, ((Real.sqrt (t v.1) : ℝ) : ℂ)‖ = ∏ v ∈ S, Real.sqrt (t v.1) := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun v _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

  have hpt : ∀ y : {y : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) // (y : K) ≠ 0},
      ‖a (y.1 : K) * ((Real.exp (-π * κ * torusForm K t (mixedEmbedding K (y.1 : K))) : ℝ) : ℂ)
          * ∏ v ∈ S, ((Real.sqrt (t v.1) : ℝ) : ℂ)‖ ≤ A * h y.1 := by
    intro y
    set Y : K := (y.1 : K) with hY
    set Q : ℝ := torusForm K t (mixedEmbedding K Y) with hQdef
    set Q1 : ℝ := torusForm K (fun _ => (1 : ℝ)) (mixedEmbedding K Y) with hQ1def
    set P : ℝ := ∏ v ∈ S, (v.1 : InfinitePlace K) Y with hPdef
    set W : ℝ := ∏ v ∈ S, Real.sqrt (t v.1) with hWdef
    have hPnn : 0 ≤ P := Finset.prod_nonneg fun v _ => apply_nonneg _ _
    have hWnn : 0 ≤ W := Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _
    have hq1 : q₀ ≤ Q1 := hq y.1 y.2
    have hQQ : β * Nr * Q1 ≤ Q := hQ t ht (mixedEmbedding K Y)

    have hA : ‖a Y * ((Real.exp (-π * κ * Q) : ℝ) : ℂ) * ∏ v ∈ S, ((Real.sqrt (t v.1) : ℝ) : ℂ)‖
        = ‖a Y‖ * Real.exp (-π * κ * Q) * W := by
      rw [norm_mul, norm_mul, hW, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]

    have hsplit : Real.exp (-π * κ * Q) = Real.exp (-π * κ' * Q) * Real.exp (-π * κ' * Q) := by
      rw [← Real.exp_add, hκ']
      congr 1
      ring

    have hD : Real.exp (-π * κ' * Q)
        ≤ ∏ v ∈ S, Real.exp (-(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2))) := by
      rw [← Real.exp_sum]
      refine Real.exp_le_exp.mpr ?_
      have hs := sum_le_torusForm K S (fun w => (htpos w).le) Y
      have : ∑ v ∈ S, -(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2))
          = -(π * κ') * ∑ v ∈ S, t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [this]
      nlinarith

    have hF : P * W * ∏ v ∈ S, Real.exp (-(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2)))
        ≤ cS := by
      rw [hPdef, hWdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, hcS, ← Finset.prod_const]
      refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
      have := sqrt_mul_mul_exp_neg_le (r := (v.1 : InfinitePlace K) Y) (htpos v.1).le hπκ
      calc (v.1 : InfinitePlace K) Y * Real.sqrt (t v.1)
            * Real.exp (-(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2)))
          = Real.sqrt (t v.1) * (v.1 : InfinitePlace K) Y
            * Real.exp (-(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2))) := by ring
        _ ≤ 1 / Real.sqrt (π * κ') := this

    have hG : Real.exp (-π * κ' * Q) ≤ Real.exp γ * Real.exp (-γ * Nr) * h y.1 := by
      rw [hh]
      simp only []
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : 0 ≤ (Nr - 1) * (Q1 - q₀) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 < π * κ' * β := by positivity
      rw [hγ]
      nlinarith [mul_nonneg h2.le h1, hQQ, mul_pos h2 hq₀]

    rw [hA, hsplit]
    calc ‖a Y‖ * (Real.exp (-π * κ' * Q) * Real.exp (-π * κ' * Q)) * W
        = (‖a Y‖ * W * Real.exp (-π * κ' * Q)) * Real.exp (-π * κ' * Q) := by ring
      _ ≤ (B * P * W * Real.exp (-π * κ' * Q)) * Real.exp (-π * κ' * Q) := by
          have : ‖a Y‖ * W ≤ B * P * W := mul_le_mul_of_nonneg_right (ha Y) hWnn
          have : ‖a Y‖ * W * Real.exp (-π * κ' * Q) ≤ B * P * W * Real.exp (-π * κ' * Q) :=
            mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)
      _ ≤ (B * cS) * Real.exp (-π * κ' * Q) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          have h1 : P * W * Real.exp (-π * κ' * Q)
              ≤ P * W * ∏ v ∈ S, Real.exp (-(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2))) :=
            mul_le_mul_of_nonneg_left hD (mul_nonneg hPnn hWnn)
          calc B * P * W * Real.exp (-π * κ' * Q) = B * (P * W * Real.exp (-π * κ' * Q)) := by ring
            _ ≤ B * cS := mul_le_mul_of_nonneg_left (h1.trans hF) hB
      _ ≤ (B * cS) * (Real.exp γ * Real.exp (-γ * Nr) * h y.1) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ = A * h y.1 := by rw [hAdef]; ring
  have hHas : HasSum (fun y : {y : ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) // (y : K) ≠ 0} => A * h y.1)
      (A * T) := hsum'.hasSum.mul_left A
  have hmain := tsum_of_norm_bounded hHas hpt
  rw [tsum_mul_right, norm_mul] at hmain
  calc _ ≤ A * T := hmain
    _ = B * cS * Real.exp γ * T * Real.exp (-γ * Nr) := by rw [hAdef]; ring

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_HighHalf
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_RayFoldIntegrable

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

p2m_open "NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
open NumberField.Units MeasureTheory Filter
open scoped nonZeroDivisors Classical Real ENNReal

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private scoped instance instCountableCoeFracIdeal :
    Countable ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  have := countable_euclideanIdealLattice K 𝔞
  Countable.of_equiv _ (idealPointEquiv K 𝔞).symm

private theorem norm_uWeight_le_one (h𝔣 : 𝔣 ≠ ⊥) (x : K) :
    ‖uWeight K 𝔣 χ S 𝔞 x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [uWeight, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero, zero_mul, norm_zero]
    exact zero_le_one
  · have hI0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) 𝔞⁻¹.isUnit.ne_zero
    rw [uWeight, norm_mul]
    have hsign : ‖signAt K S x‖ = 1 := by
      have h := normSq_signAt S hx
      rw [Complex.normSq_eq_norm_sq] at h
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (h.trans (one_pow 2).symm)
    by_cases hIc : Units.mk0 _ hI0 ∈ coprimeToModulus K 𝔣
    · rw [norm_chiIdeal_of_mem χ h𝔣 hI0 hIc, hsign, one_mul]
    · rw [chiIdeal_eq_zero_of_not_mem χ hI0 hIc, norm_zero, zero_mul]
      exact zero_le_one

private theorem measurable_rayFoldSummand_left (c : ℝ) (x : K) :
    Measurable fun t => rayFoldSummand K 𝔣 χ S 𝔞 c t x := by
  unfold rayFoldSummand
  exact (measurable_const.mul measurable_const).mul (Complex.measurable_ofReal.comp
    ((measurable_torusForm_left K (mixedEmbedding K x)).const_mul (-Real.pi * c)).exp)

private theorem measurable_rayMellinWeight (s : ℂ) : Measurable (rayMellinWeight K S s) := by
  unfold rayMellinWeight raySWeight
  exact ((Complex.measurable_ofReal.comp (continuous_torusNorm K).measurable).pow_const _).mul
    (Finset.measurable_prod S fun v _ => Complex.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp (measurable_pi_apply _)))

private theorem measurable_rayFoldMellinIntegrand (c : ℝ) (s : ℂ) :
    Measurable (rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s) := by
  unfold rayFoldMellinIntegrand
  refine Measurable.mul ?_ (measurable_rayMellinWeight K S s)
  exact Measurable.tsum fun x => measurable_rayFoldSummand_left K 𝔣 χ S 𝔞 c x

private def rayMajKernel (c : ℝ) (y : K) (σ : ℝ) (t : realSpace K) : ℝ :=
  (∏ v ∈ S, ((v : InfinitePlace K) y * Real.sqrt (t v)))
    * Real.exp (-Real.pi * c * torusForm K t (mixedEmbedding K y)) * (torusNorm K t) ^ (σ / 2)

private theorem enorm_rayFoldSummand_mul_rayMellinWeight_le (h𝔣 : 𝔣 ≠ ⊥) (c : ℝ) (s : ℂ) (y : K)
    {t : realSpace K} (ht : t ∈ orthant K) :
    ‖rayFoldSummand K 𝔣 χ S 𝔞 c t y * rayMellinWeight K S s t‖ₑ
      ≤ ENNReal.ofReal (rayMajKernel K S c y s.re t) := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rayFoldSummand, rayMellinWeight, raySWeight, rayMajKernel,
    norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos (torusNorm_pos K ht), Complex.div_ofNat_re,
    show ‖∏ v ∈ S, ((Real.sqrt (t v) : ℝ) : ℂ)‖ = ∏ v ∈ S, Real.sqrt (t v) by
      rw [← Complex.ofReal_prod, Complex.norm_real,
        Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)],
    show ‖∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ)‖ = ∏ v ∈ S, (v : InfinitePlace K) y by
      rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
      exact Finset.prod_congr rfl fun v _ => by rw [← norm_embedding_of_isReal v.2, Real.norm_eq_abs],
    show (∏ v ∈ S, (v : InfinitePlace K) y * Real.sqrt (t v))
        = (∏ v ∈ S, (v : InfinitePlace K) y) * ∏ v ∈ S, Real.sqrt (t v) from Finset.prod_mul_distrib]
  have hR : (0:ℝ) ≤ (∏ v ∈ S, (v : InfinitePlace K) y)
      * Real.exp (-π * c * torusForm K t (mixedEmbedding K y))
      * (torusNorm K t ^ (s.re / 2)) * ∏ v ∈ S, Real.sqrt (t v) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => apply_nonneg _ y)
      (Real.exp_nonneg _)) (Real.rpow_nonneg (torusNorm_pos K ht).le _))
      (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
  calc ‖uWeight K 𝔣 χ S 𝔞 y‖ * (∏ v ∈ S, (v : InfinitePlace K) y)
          * Real.exp (-π * c * torusForm K t (mixedEmbedding K y))
          * (torusNorm K t ^ (s.re / 2) * ∏ v ∈ S, Real.sqrt (t v))
      = ‖uWeight K 𝔣 χ S 𝔞 y‖ * ((∏ v ∈ S, (v : InfinitePlace K) y)
          * Real.exp (-π * c * torusForm K t (mixedEmbedding K y))
          * (torusNorm K t ^ (s.re / 2)) * ∏ v ∈ S, Real.sqrt (t v)) := by ring
    _ ≤ 1 * ((∏ v ∈ S, (v : InfinitePlace K) y)
          * Real.exp (-π * c * torusForm K t (mixedEmbedding K y))
          * (torusNorm K t ^ (s.re / 2)) * ∏ v ∈ S, Real.sqrt (t v)) :=
        mul_le_mul_of_nonneg_right (norm_uWeight_le_one K 𝔣 χ S 𝔞 h𝔣 y) hR
    _ = ((∏ v ∈ S, (v : InfinitePlace K) y) * ∏ v ∈ S, Real.sqrt (t v))
          * Real.exp (-π * c * torusForm K t (mixedEmbedding K y))
          * torusNorm K t ^ (s.re / 2) := by ring

private def rayMajRate (c : ℝ) (y : K) (w : InfinitePlace K) : ℝ :=
  Real.pi * c * (mult w : ℝ) * (w y) ^ 2

omit [NumberField K] in
private theorem rayMajRate_pos {c : ℝ} (hc : 0 < c) {y : K} (hy : y ≠ 0) (w : InfinitePlace K) :
    0 < rayMajRate K c y w := by
  unfold rayMajRate
  have h2 : (0 : ℝ) < mult w := by exact_mod_cast (mult_pos (w := w))
  have h3 : 0 < w y := pos_iff.mpr hy
  positivity

private def rayMajExp (σ : ℝ) (w : InfinitePlace K) : ℝ :=
  orbitExp K σ w + if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℝ)/2 else 0) else 0

omit [NumberField K] in
private theorem rayMajExp_pos {σ : ℝ} (hσ : 0 < σ) (w : InfinitePlace K) : 0 < rayMajExp K S σ w := by
  unfold rayMajExp
  have h := orbitExp_pos K hσ w
  split <;> [split <;> linarith; linarith]

private def rayMajFactor (c : ℝ) (y : K) (σ : ℝ) (w : InfinitePlace K) (x : ℝ) : ℝ :=
  ((w y) ^ if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℕ) else 0) else 0)
    * (x ^ (rayMajExp K S σ w - 1) * Real.exp (-(rayMajRate K c y w * x)))

omit [NumberField K] in
private theorem rayMajFactor_nonneg (c : ℝ) (y : K) (σ : ℝ) (w : InfinitePlace K) {x : ℝ} (hx : 0 < x) :
    0 ≤ rayMajFactor K S c y σ w x :=
  mul_nonneg (pow_nonneg (apply_nonneg w y) _)
    (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_nonneg _))

omit [NumberField K] in
private theorem integrableOn_rayMajFactor {c : ℝ} (hc : 0 < c) {y : K} (hy : y ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (w : InfinitePlace K) : IntegrableOn (rayMajFactor K S c y σ w) (Set.Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => x ^ (rayMajExp K S σ w - 1)
      * Real.exp (-(rayMajRate K c y w * x))) (Set.Ioi 0) := by
    have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := rayMajExp K S σ w - 1)
      (p := 1) (b := rayMajRate K c y w)
      (by linarith [rayMajExp_pos K S hσ w]) one_pos (rayMajRate_pos K hc hy w)
    refine h0.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  exact h.const_mul _

private theorem prod_sqrt_eq_prod_rpow_indicator (t : realSpace K) (y : K) :
    (∏ v ∈ S, ((v : InfinitePlace K) y * Real.sqrt (t v)))
      = ∏ w : InfinitePlace K,
          ((w y) ^ (if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℕ) else 0) else 0)
            * t w ^ (if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℝ)/2 else 0) else 0)) := by
  classical
  rw [prod_eq_prod_mul_prod,
    show (∏ v : {w : InfinitePlace K // IsComplex w},
        ((v.1 y) ^ (if h : (v:InfinitePlace K).IsReal then
            (if ⟨v.1, h⟩ ∈ S then (1:ℕ) else 0) else 0)
          * t v.1 ^ (if h : (v:InfinitePlace K).IsReal then
            (if ⟨v.1, h⟩ ∈ S then (1:ℝ)/2 else 0) else 0))) = 1 from
      Finset.prod_eq_one fun v _ => by
        rw [dif_neg (not_isReal_iff_isComplex.mpr v.2), dif_neg (not_isReal_iff_isComplex.mpr v.2),
          pow_zero, Real.rpow_zero, mul_one],
    mul_one,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset {w : InfinitePlace K // IsReal w})
      (· ∈ S),
    Finset.filter_mem_eq_inter, Finset.univ_inter,
    show (∏ v ∈ Finset.filter (¬ · ∈ S)
          (Finset.univ : Finset {w : InfinitePlace K // IsReal w}),
        ((v.1 y) ^ (if h : (v:InfinitePlace K).IsReal then
            (if ⟨v.1, h⟩ ∈ S then (1:ℕ) else 0) else 0)
          * t v.1 ^ (if h : (v:InfinitePlace K).IsReal then
            (if ⟨v.1, h⟩ ∈ S then (1:ℝ)/2 else 0) else 0))) = 1 from
      Finset.prod_eq_one fun v hv => by
        rw [dif_pos v.2, if_neg (Finset.mem_filter.mp hv).2,
          dif_pos v.2, if_neg (Finset.mem_filter.mp hv).2, pow_zero, Real.rpow_zero, mul_one],
    mul_one]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvS : (⟨v.1, v.2⟩ : {w : InfinitePlace K // IsReal w}) ∈ S := by simpa using hv
  rw [dif_pos v.2, if_pos hvS, dif_pos v.2, if_pos hvS, pow_one, ← Real.sqrt_eq_rpow]

private theorem density_mul_rayMajKernel_eq_prod (c : ℝ) (y : K) (σ : ℝ) {t : realSpace K}
    (ht : t ∈ orthant K) :
    (∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹).toReal * rayMajKernel K S c y σ t
      = ∏ w : InfinitePlace K, rayMajFactor K S c y σ w (t w) := by
  have hexp : Real.exp (-π * c * torusForm K t (mixedEmbedding K y))
      = ∏ w : InfinitePlace K, Real.exp (-(rayMajRate K c y w * t w)) := by
    rw [torusForm, ← Real.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [normAtPlace_apply, rayMajRate]; ring
  rw [ENNReal.toReal_prod, rayMajKernel, hexp, torusNorm_rpow_eq_prod K ht,
    prod_sqrt_eq_prod_rpow_indicator K S t y,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (ht w).le), rayMajFactor, rayMajExp,
    Real.rpow_sub_one (ht w).ne', Real.rpow_add (ht w), div_eq_mul_inv]
  ring

private theorem integrable_prod_rayMajFactor {c : ℝ} (hc : 0 < c) {y : K} (hy : y ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : realSpace K => ∏ w, rayMajFactor K S c y σ w (t w))
      ((volume : Measure (realSpace K)).restrict {t : realSpace K | ∀ w, 0 < t w}) := by
  rw [volume_restrict_setOf_pos]
  exact Integrable.fintype_prod (f := fun w => rayMajFactor K S c y σ w)
    fun w => integrableOn_rayMajFactor K S hc hy hσ w

private def rayMajGammaConst (c : ℝ) (σ : ℝ) : ℝ :=
  ∏ w : InfinitePlace K, (Real.pi * c * (mult w : ℝ)) ^ (-rayMajExp K S σ w)
    * Real.Gamma (rayMajExp K S σ w)

private theorem rayMajGammaConst_pos {c : ℝ} (hc : 0 < c) {σ : ℝ} (hσ : 0 < σ) :
    0 < rayMajGammaConst K S c σ := by
  unfold rayMajGammaConst
  refine Finset.prod_pos fun w _ => mul_pos ?_ (Real.Gamma_pos_of_pos (rayMajExp_pos K S hσ w))
  refine Real.rpow_pos_of_pos ?_ _
  have h2 : (0 : ℝ) < mult w := by exact_mod_cast (mult_pos (w := w))
  positivity

omit [NumberField K] in

private theorem pow_mul_one_div_rayMajRate_rpow {c : ℝ} (hc : 0 < c) {y : K} (hy : y ≠ 0) (σ : ℝ)
    (w : InfinitePlace K) :
    ((w y) ^ if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℕ) else 0) else 0)
        * (1 / rayMajRate K c y w) ^ rayMajExp K S σ w
      = (Real.pi * c * (mult w : ℝ)) ^ (-rayMajExp K S σ w) * (w y) ^ (-(mult w : ℝ) * σ) := by
  have hwy : 0 < w y := pos_iff.mpr hy
  have hA : 0 ≤ Real.pi * c * (mult w : ℝ) := by
    have h2 : (0 : ℝ) < mult w := by exact_mod_cast (mult_pos (w := w))
    positivity
  have hB : 0 ≤ (w y) ^ 2 := sq_nonneg _
  rw [rayMajRate, one_div, Real.inv_rpow (mul_nonneg hA hB), ← Real.rpow_neg (mul_nonneg hA hB),
    Real.mul_rpow hA hB, ← mul_assoc, mul_comm ((w y) ^ _) _, mul_assoc]
  congr 1
  rw [← Real.rpow_natCast (w y) 2, ← Real.rpow_mul hwy.le,
    ← Real.rpow_natCast (w y) (if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℕ) else 0) else 0),
    ← Real.rpow_add hwy]
  congr 1
  rw [rayMajExp, orbitExp]
  have : ((if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℕ) else 0) else 0 : ℕ) : ℝ)
      = (if h : w.IsReal then (if ⟨w, h⟩ ∈ S then (1:ℝ)/2 else 0) else 0) * 2 := by
    split <;> [split <;> norm_num; norm_num]
  rw [this]; ring

omit [NumberField K] in
private theorem integral_rayMajFactor {c : ℝ} (hc : 0 < c) {y : K} (hy : y ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (w : InfinitePlace K) :
    ∫ x in Set.Ioi 0, rayMajFactor K S c y σ w x
      = ((Real.pi * c * (mult w : ℝ)) ^ (-rayMajExp K S σ w) * Real.Gamma (rayMajExp K S σ w))
        * (w y) ^ (-(mult w : ℝ) * σ) := by
  unfold rayMajFactor
  rw [integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (rayMajExp_pos K S hσ w) (rayMajRate_pos K hc hy w),
    ← mul_assoc, pow_mul_one_div_rayMajRate_rpow K S hc hy σ w, mul_right_comm]

private theorem integral_prod_rayMajFactor {c : ℝ} (hc : 0 < c) {y : K} (hy : y ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in {t : realSpace K | ∀ w, 0 < t w}, ∏ w, rayMajFactor K S c y σ w (t w)
      = rayMajGammaConst K S c σ * (∏ w : InfinitePlace K, (w y) ^ mult w) ^ (-σ) := by
  rw [volume_restrict_setOf_pos,
    integral_fintype_prod_eq_prod (𝕜 := ℝ) (f := fun w => rayMajFactor K S c y σ w)
      (μ := fun _ => (volume : Measure ℝ).restrict (Set.Ioi 0))]
  simp_rw [integral_rayMajFactor K S hc hy hσ]
  rw [rayMajGammaConst, ← Real.finsetProd_rpow _ _ (fun w _ => pow_nonneg (apply_nonneg w y) _),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Real.rpow_natCast (w y) (mult w), ← Real.rpow_mul (apply_nonneg w y), mul_neg, neg_mul]

private theorem measurable_rayMajKernel (c : ℝ) (y : K) (σ : ℝ) : Measurable (rayMajKernel K S c y σ) := by
  unfold rayMajKernel
  exact (((Finset.measurable_prod S fun v _ => measurable_const.mul
    (Real.continuous_sqrt.measurable.comp (measurable_pi_apply _)))).mul
    (Real.measurable_exp.comp ((measurable_torusForm_left K _).const_mul _))).mul
    (((continuous_torusNorm K).measurable).pow_const _)

private theorem setLIntegral_orthant_rayMajKernel_eq {c : ℝ} (hc : 0 < c) {y : K} (hy : y ≠ 0) {σ : ℝ}
    (hσ : 0 < σ) :
    ∫⁻ t in orthant K, ENNReal.ofReal (rayMajKernel K S c y σ t) ∂(torusHaar K)
      = ENNReal.ofReal (rayMajGammaConst K S c σ
          * (∏ w : InfinitePlace K, (w y) ^ mult w) ^ (-σ)) := by
  have hS := measurableSet_setOf_pos K
  have hk : Measurable fun t => ENNReal.ofReal (rayMajKernel K S c y σ t) :=
    ENNReal.measurable_ofReal.comp (measurable_rayMajKernel K S c y σ)
  have h2 : 0 ≤ᵐ[(volume : Measure (realSpace K)).restrict {t : realSpace K | ∀ w, 0 < t w}]
      fun t => ∏ w, rayMajFactor K S c y σ w (t w) := by
    filter_upwards [ae_restrict_mem hS] with t ht
    exact Finset.prod_nonneg fun w _ => rayMajFactor_nonneg K S c y σ w (ht w)
  rw [orthant_def, torusHaar_def,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_torusDensity K) hk hS,
    ← integral_prod_rayMajFactor K S hc hy hσ,
    ofReal_integral_eq_lintegral_ofReal (integrable_prod_rayMajFactor K S hc hy hσ) h2]
  refine setLIntegral_congr_fun hS fun t ht => ?_
  rw [Pi.mul_apply, ← density_mul_rayMajKernel_eq_prod K S c y σ ht,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (torusDensity_lt_top K t).ne]

private theorem rayMajKernel_unit_mul (c : ℝ) (u : (𝓞 K)ˣ) (x : K) (σ : ℝ) (t : realSpace K) :
    rayMajKernel K S c (((u : 𝓞 K) : K) * x) σ t = rayMajKernel K S c x σ (unitTorus K u t) := by
  unfold rayMajKernel
  rw [torusForm_mixedEmbedding_unit_mul K u t x, torusNorm_unitTorus K u t]
  congr 2
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_mul, unitTorus_apply,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (apply_nonneg (v : InfinitePlace K) _)]
  ring

private noncomputable def fracIdealGen
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) : K :=
  haveI : ((𝔞 * FractionalIdeal.mk0 K I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      : Submodule (𝓞 K) K).IsPrincipal :=
    ClassGroup.mk_eq_one_iff.mp (by rw [map_mul, ClassGroup.mk_mk0, I.2, mul_inv_cancel])
  Submodule.IsPrincipal.generator
    ((𝔞 * FractionalIdeal.mk0 K I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule (𝓞 K) K)

private theorem instIsPrincipal_fracIdealProd
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) :
    ((𝔞 * FractionalIdeal.mk0 K I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      : Submodule (𝓞 K) K).IsPrincipal :=
  ClassGroup.mk_eq_one_iff.mp (by rw [map_mul, ClassGroup.mk_mk0, I.2, mul_inv_cancel])

private theorem spanSingleton_fracIdealGen
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (fracIdealGen K 𝔞 I)
      = ((𝔞 * FractionalIdeal.mk0 K I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  haveI := instIsPrincipal_fracIdealProd K 𝔞 I
  refine FractionalIdeal.coeToSubmodule_injective ?_
  show (↑(FractionalIdeal.spanSingleton (𝓞 K)⁰ (fracIdealGen K 𝔞 I)) : Submodule (𝓞 K) K) = _
  rw [FractionalIdeal.coe_spanSingleton, fracIdealGen, Submodule.IsPrincipal.span_singleton_generator]

private theorem fracIdealGen_ne_zero
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) :
    fracIdealGen K 𝔞 I ≠ 0 := fun h =>
  (𝔞 * FractionalIdeal.mk0 K I).ne_zero
    (by rw [← spanSingleton_fracIdealGen K 𝔞 I, h, FractionalIdeal.spanSingleton_zero])

private theorem fracIdealGen_mem
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) :
    fracIdealGen K 𝔞 I ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h1 : fracIdealGen K 𝔞 I ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (fracIdealGen K 𝔞 I) :=
    FractionalIdeal.mem_spanSingleton_self _ _
  rw [spanSingleton_fracIdealGen K 𝔞 I, Units.val_mul, FractionalIdeal.coe_mk0] at h1
  exact (mul_le_mul_right FractionalIdeal.coeIdeal_le_one (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
    |>.trans_eq (mul_one _)) h1

private theorem prod_pow_mult_fracIdealGen
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) :
    ∏ w : InfinitePlace K, (w (fracIdealGen K 𝔞 I)) ^ mult w
      = FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
          * (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) := by
  have h := prod_eq_abs_norm (fracIdealGen K 𝔞 I)
  rw [show |(Algebra.norm ℚ) (fracIdealGen K 𝔞 I)|
      = FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (fracIdealGen K 𝔞 I)) from
        (FractionalIdeal.absNorm_span_singleton (R := 𝓞 K) _).symm,
    spanSingleton_fracIdealGen K 𝔞 I, Units.val_mul, map_mul, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm] at h
  push_cast at h ⊢
  exact h

private noncomputable def fracIdealOrbitEquiv :
    ({I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹} × (𝓞 K)ˣ)
      ≃ {x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (x : K) ≠ 0} :=
  Equiv.ofBijective
    (fun p => ⟨⟨((p.2 : 𝓞 K) : K) * fracIdealGen K 𝔞 p.1, by
        have hmem : fracIdealGen K 𝔞 p.1 ∈ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
          fracIdealGen_mem K 𝔞 p.1
        have := ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).smul_mem (p.2 : 𝓞 K) hmem
        rw [Algebra.smul_def] at this
        exact this⟩,
      mul_ne_zero (by
          rw [RingOfIntegers.coe_eq_algebraMap, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
          exact p.2.ne_zero)
        (fracIdealGen_ne_zero K 𝔞 p.1)⟩)
    (by
      constructor
      · rintro ⟨I₁, u₁⟩ ⟨I₂, u₂⟩ h
        have hK : ((u₁ : 𝓞 K) : K) * fracIdealGen K 𝔞 I₁
            = ((u₂ : 𝓞 K) : K) * fracIdealGen K 𝔞 I₂ :=
          congrArg (fun z => (z.1 : K)) h
        have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ (fracIdealGen K 𝔞 I₁)
            = FractionalIdeal.spanSingleton (𝓞 K)⁰ (fracIdealGen K 𝔞 I₂) := by
          have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰
              (((u₁ : 𝓞 K) : K) * fracIdealGen K 𝔞 I₁)
              = FractionalIdeal.spanSingleton (𝓞 K)⁰
              (((u₂ : 𝓞 K) : K) * fracIdealGen K 𝔞 I₂) := by rw [hK]
          rwa [← FractionalIdeal.spanSingleton_mul_spanSingleton,
            ← FractionalIdeal.spanSingleton_mul_spanSingleton,
            show FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u₁ : 𝓞 K) : K) = 1 by
              rw [RingOfIntegers.coe_eq_algebraMap, ← FractionalIdeal.coeIdeal_span_singleton,
                Ideal.span_singleton_eq_top.mpr u₁.isUnit, FractionalIdeal.coeIdeal_top],
            show FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u₂ : 𝓞 K) : K) = 1 by
              rw [RingOfIntegers.coe_eq_algebraMap, ← FractionalIdeal.coeIdeal_span_singleton,
                Ideal.span_singleton_eq_top.mpr u₂.isUnit, FractionalIdeal.coeIdeal_top],
            one_mul, one_mul] at h1
        rw [spanSingleton_fracIdealGen, spanSingleton_fracIdealGen] at hsp
        have hI12 : I₁ = I₂ := by
          have hunits := mul_left_cancel (a := 𝔞) (Units.ext hsp)
          have hval := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
            (u : FractionalIdeal (𝓞 K)⁰ K)) hunits
          simp only [FractionalIdeal.coe_mk0] at hval
          exact Subtype.ext (Subtype.ext (FractionalIdeal.coeIdeal_inj' le_rfl |>.mp hval))
        subst hI12
        exact Prod.ext rfl (Units.ext (RingOfIntegers.coe_injective
          (mul_right_cancel₀ (fracIdealGen_ne_zero K 𝔞 I₁) hK)))
      · rintro ⟨⟨x, hx𝔞⟩, hx0⟩
        have hsp_le : (𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
            * FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ 1 := by
          calc (𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ).1 * FractionalIdeal.spanSingleton (𝓞 K)⁰ x
              ≤ (𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ).1 * ↑𝔞 :=
                mul_le_mul_right (FractionalIdeal.spanSingleton_le_iff_mem.mpr hx𝔞) _
            _ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hsp_le
        have hJ0 : J ∈ (Ideal (𝓞 K))⁰ := by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          intro h0
          apply hx0
          have h1 : ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
              * FractionalIdeal.spanSingleton (𝓞 K)⁰ x = 0 := by
            rw [← hJ, h0, Ideal.zero_eq_bot, FractionalIdeal.coeIdeal_bot]
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h (Units.ne_zero 𝔞⁻¹)
          · exact FractionalIdeal.spanSingleton_eq_zero_iff.mp h
        have hprod : ((𝔞 * FractionalIdeal.mk0 K (⟨J, hJ0⟩ : (Ideal (𝓞 K))⁰)
            : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
            = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
          rw [Units.val_mul, FractionalIdeal.coe_mk0]
          calc (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * ↑J
              = (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
                  * FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by rw [hJ]
            _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
                rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
        have hJcls : ClassGroup.mk0 (⟨J, hJ0⟩ : (Ideal (𝓞 K))⁰) = (ClassGroup.mk K 𝔞)⁻¹ := by
          rw [← ClassGroup.mk_mk0 K, eq_inv_iff_mul_eq_one, ← map_mul, mul_comm,
            ClassGroup.mk_eq_one_iff]
          exact ⟨x, by rw [hprod, FractionalIdeal.coe_spanSingleton]⟩
        have hgen : FractionalIdeal.spanSingleton (𝓞 K)⁰ (fracIdealGen K 𝔞 ⟨⟨J, hJ0⟩, hJcls⟩)
            = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
          rw [spanSingleton_fracIdealGen]; exact hprod
        obtain ⟨u, hu⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton.mp hgen)
        refine ⟨⟨⟨⟨J, hJ0⟩, hJcls⟩, u⟩, ?_⟩
        exact Subtype.ext (Subtype.ext (by
          simpa [Units.smul_def, Algebra.smul_def, mul_comm, RingOfIntegers.coe_eq_algebraMap] using hu))
      )

private theorem fracIdealOrbitEquiv_apply_val
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) (u : (𝓞 K)ˣ) :
    ((fracIdealOrbitEquiv K 𝔞 (I, u)).1 : K) = ((u : 𝓞 K) : K) * fracIdealGen K 𝔞 I := rfl

private theorem fracIdealOrbitEquiv_one_val
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) :
    ((fracIdealOrbitEquiv K 𝔞 (I, 1)).1 : K) = fracIdealGen K 𝔞 I := by
  rw [fracIdealOrbitEquiv_apply_val, Units.val_one, RingOfIntegers.coe_eq_algebraMap, map_one,
    one_mul]

private theorem fracIdealOrbitEquiv_apply_coe
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) (u : (𝓞 K)ˣ)
    (t : realSpace K) (σ : ℝ) (c : ℝ) :
    rayMajKernel K S c ((fracIdealOrbitEquiv K 𝔞 (I, u)).1 : K) σ t
      = rayMajKernel K S c ((fracIdealOrbitEquiv K 𝔞 (I, 1)).1 : K) σ (unitTorus K u t) := by
  rw [fracIdealOrbitEquiv_apply_val, fracIdealOrbitEquiv_one_val,
    rayMajKernel_unit_mul K S c u (fracIdealGen K 𝔞 I)]

private theorem rayFoldSummand_zero (c : ℝ) (t : realSpace K) :
    rayFoldSummand K 𝔣 χ S 𝔞 c t 0 = 0 := by
  unfold rayFoldSummand
  rw [show uWeight K 𝔣 χ S 𝔞 0 = 0 by
    rw [uWeight, FractionalIdeal.spanSingleton_zero, zero_mul, M4aP2.chiIdeal_zero, zero_mul],
    zero_mul, zero_mul]

private theorem ennreal_tsum_option {α : Type*} (f : Option α → ℝ≥0∞) :
    ∑' o, f o = f none + ∑' a, f (some a) := by
  let e : Option α ≃ α ⊕ Unit := Equiv.optionEquivSumPUnit α
  have h1 : ∑' a : α, f (e.symm (Sum.inl a)) = ∑' a, f (some a) :=
    tsum_congr fun a => congrArg f (Equiv.optionEquivSumPUnit_symm_inl a)
  have h2 : ∑' u : Unit, f (e.symm (Sum.inr u)) = f none := by
    rw [tsum_eq_single PUnit.unit (fun b' hb' => absurd (Subsingleton.elim _ _) hb'),
      show e.symm (Sum.inr PUnit.unit) = none from Equiv.optionEquivSumPUnit_symm_inr _]
  calc ∑' o, f o = ∑' x : α ⊕ Unit, f (e.symm x) := (e.symm.tsum_eq _).symm
    _ = (∑' a : α, f (e.symm (Sum.inl a))) + ∑' u : Unit, f (e.symm (Sum.inr u)) :=
        (HasSum.sum ENNReal.summable.hasSum ENNReal.summable.hasSum).tsum_eq
    _ = f none + ∑' a, f (some a) := by rw [h1, h2, add_comm]

private noncomputable def fracIdealNonzeroEquiv :
    ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      ≃ Option {x : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (x : K) ≠ 0} :=
  (Equiv.optionSubtypeNe (⟨0, FractionalIdeal.zero_mem _⟩ : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K))).symm.trans
    (Equiv.optionCongr (Equiv.subtypeEquivRight fun _x =>
      ⟨fun h h0 => h (Subtype.ext h0), fun h h0 => h (congrArg Subtype.val h0)⟩))

private theorem fracIdealNonzeroEquiv_symm_none :
    (((fracIdealNonzeroEquiv K 𝔞).symm none : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K) = 0 := by
  rfl

private theorem fracIdealNonzeroEquiv_symm_some (x : {x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (x : K) ≠ 0}) :
    (((fracIdealNonzeroEquiv K 𝔞).symm (some x) : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K)
      = (x.1 : K) := by
  rfl

private theorem tsum_lintegral_foldDomain_enorm_rayFoldSummand_ne_top
    (h𝔣 : 𝔣 ≠ ⊥) (c : ℝ) (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
        ∫⁻ t in foldDomain K, ‖rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K)
          * rayMellinWeight K S s t‖ₑ ∂(torusHaar K)) ≠ ⊤ := by
  have hs0 : 0 < s.re := one_pos.trans hs

  rw [← (fracIdealNonzeroEquiv K 𝔞).symm.tsum_eq, ennreal_tsum_option]
  have hz : ∫⁻ t in foldDomain K, ‖rayFoldSummand K 𝔣 χ S 𝔞 c t
        (((fracIdealNonzeroEquiv K 𝔞).symm none : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K)
      * rayMellinWeight K S s t‖ₑ ∂(torusHaar K) = 0 := by
    simp only [fracIdealNonzeroEquiv_symm_none, rayFoldSummand_zero, zero_mul, enorm_zero,
      lintegral_zero]
  rw [hz, zero_add]

  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum
    (g := fun x : {x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (x : K) ≠ 0} =>
      ∫⁻ t in foldDomain K, ENNReal.ofReal (rayMajKernel K S c (x.1 : K) s.re t) ∂(torusHaar K))
    fun x => ?_)
  ·
    rw [← (fracIdealOrbitEquiv K 𝔞).tsum_eq, ENNReal.tsum_prod']

    have step : ∀ I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹},
        (∑' u : (𝓞 K)ˣ, ∫⁻ t in foldDomain K,
            ENNReal.ofReal (rayMajKernel K S c ((fracIdealOrbitEquiv K 𝔞 (I, u)).1 : K) s.re t)
            ∂(torusHaar K))
          = (torsionOrder K : ℝ≥0∞)
            * ENNReal.ofReal (rayMajGammaConst K S c s.re
              * (∏ w : InfinitePlace K,
                  (w ((fracIdealOrbitEquiv K 𝔞 (I, 1)).1 : K)) ^ mult w) ^ (-s.re)) := by
      intro I
      have h5 := tsum_units_setLIntegral_foldDomain K
        (fun t => ENNReal.ofReal (rayMajKernel K S c ((fracIdealOrbitEquiv K 𝔞 (I, 1)).1 : K) s.re t))
      refine (tsum_congr fun u => setLIntegral_congr_fun (measurableSet_foldDomain K) fun t _ =>
        congrArg ENNReal.ofReal (fracIdealOrbitEquiv_apply_coe K S 𝔞 I u t s.re c)).trans ?_
      rw [h5, setLIntegral_orthant_rayMajKernel_eq K S hc (fracIdealOrbitEquiv K 𝔞 (I, 1)).2 hs0]
    refine (tsum_congr step).trans_ne ?_

    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_ne_top (by exact_mod_cast ENNReal.natCast_ne_top _) ?_
    refine tsum_ofReal_ne_top_of_summable
        (fun I => mul_nonneg (rayMajGammaConst_pos K S hc hs0).le
          (Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (apply_nonneg _ _) _) _)) ?_
    have hsum := (summable_class_rpow K ((ClassGroup.mk K 𝔞)⁻¹) hs).mul_left
      (rayMajGammaConst K S c s.re
        * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ (-s.re))
    refine hsum.congr fun I => ?_
    rw [fracIdealOrbitEquiv_one_val, prod_pow_mult_fracIdealGen K 𝔞 I,
      Real.mul_rpow (by exact_mod_cast FractionalIdeal.absNorm_nonneg _) (Nat.cast_nonneg _),
      ← mul_assoc]
  ·
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_foldDomain K)] with t ht
    have hta : t ∈ orthant K := foldDomain_subset_orthant K ht
    calc ‖rayFoldSummand K 𝔣 χ S 𝔞 c t
              (((fracIdealNonzeroEquiv K 𝔞).symm (some x) : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K)
            * rayMellinWeight K S s t‖ₑ
        ≤ ENNReal.ofReal (rayMajKernel K S c
            (((fracIdealNonzeroEquiv K 𝔞).symm (some x)
              : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K) s.re t) :=
          enorm_rayFoldSummand_mul_rayMellinWeight_le K 𝔣 χ S 𝔞 h𝔣 c s _ hta
      _ = ENNReal.ofReal (rayMajKernel K S c (x.1 : K) s.re t) := by
          rw [fracIdealNonzeroEquiv_symm_some]

private theorem integrableOn_foldDomain_rayFoldMellinIntegrand
    (h𝔣 : 𝔣 ≠ ⊥) (c : ℝ) (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s) (foldDomain K) (torusHaar K) := by
  refine ⟨(measurable_rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s).aestronglyMeasurable.restrict, ?_⟩
  have hmeas : ∀ x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
      Measurable fun t => rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K) * rayMellinWeight K S s t :=
    fun x => (measurable_rayFoldSummand_left K 𝔣 χ S 𝔞 c x).mul (measurable_rayMellinWeight K S s)
  refine lt_of_le_of_lt ?_
    (tsum_lintegral_foldDomain_enorm_rayFoldSummand_ne_top K 𝔣 χ S 𝔞 h𝔣 c hc hs).lt_top
  calc ∫⁻ t in foldDomain K, ‖rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t‖ₑ ∂(torusHaar K)
      = ∫⁻ t in foldDomain K, ‖(∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
            rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K) * rayMellinWeight K S s t)‖ₑ ∂(torusHaar K) := by
        refine setLIntegral_congr_fun (measurableSet_foldDomain K) fun t _ => ?_
        rw [rayFoldMellinIntegrand, ← tsum_mul_right]
    _ ≤ ∫⁻ t in foldDomain K, (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
            ‖rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K) * rayMellinWeight K S s t‖ₑ) ∂(torusHaar K) :=
        lintegral_mono fun t => enorm_tsum_le_tsum_enorm
    _ = ∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∫⁻ t in foldDomain K,
            ‖rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K) * rayMellinWeight K S s t‖ₑ ∂(torusHaar K) :=
        lintegral_tsum fun x => ((hmeas x).enorm).aemeasurable

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_RayFoldIntegrable
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTheta_DualDict

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic MeasureTheory"
open scoped nonZeroDivisors Classical FourierTransform InnerProductSpace

variable (K : Type) [Field K] [NumberField K]

private def realUnit (v : {w : InfinitePlace K // IsReal w}) : euclidean.mixedSpace K :=
  euclidean.stdOrthonormalBasis K (Sum.inl v)

private theorem orthonormal_realUnit : Orthonormal ℝ (realUnit K) :=
  (euclidean.stdOrthonormalBasis K).orthonormal.comp _ Sum.inl_injective

private theorem inner_realUnit (v : {w : InfinitePlace K // IsReal w}) (z : euclidean.mixedSpace K) :
    ⟪realUnit K v, z⟫_ℝ = z.fst v := by
  rw [realUnit, ← OrthonormalBasis.repr_apply_apply, euclideanRepr_inl]

private theorem polyS_realUnit (S : Finset {w : InfinitePlace K // IsReal w}) (z : euclidean.mixedSpace K) :
    polyS (realUnit K) S z = ∏ v ∈ S, ((z.fst v : ℝ) : ℂ) :=
  Finset.prod_congr rfl fun v _ => by rw [inner_realUnit]

private theorem mixedDil_symm_apply_fst (z : euclidean.mixedSpace K) : ((mixedDil K).symm z).fst = z.fst := by
  have h := mixedDil_apply_fst K ((mixedDil K).symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

private def dualPt (y : K) : euclidean.mixedSpace K :=
  (mixedDil K).symm (mixedConjDil K ((euclidean.toMixed K).symm (mixedEmbedding K y)))

private theorem inner_dil_dualPt (r y : K) :
    ⟪mixedDil K ((euclidean.toMixed K).symm (mixedEmbedding K r)), dualPt K y⟫_ℝ
      = ((Algebra.trace ℚ K (r * y) : ℚ) : ℝ) := by
  rw [dualPt, inner_mixedDil, LinearEquiv.apply_symm_apply, inner_mixedConjDil_eq_trace]

private theorem fourierChar_inner_dil_dualPt (r y : K) :
    ((𝐞 ⟪mixedDil K ((euclidean.toMixed K).symm (mixedEmbedding K r)), dualPt K y⟫_ℝ : Circle) : ℂ)
      = addChar K (r * y) := by
  rw [inner_dil_dualPt, Real.fourierChar_apply, addChar]
  push_cast
  ring_nf

private theorem dualPt_fst (y : K) (v : {w : InfinitePlace K // IsReal w}) : (dualPt K y).fst v = embedding_of_isReal v.2 y := by
  rw [dualPt, mixedDil_symm_apply_fst, mixedConjDil_apply_fst, toMixed_symm_fst, mixedEmbedding_apply_isReal]

private theorem polyS_realUnit_dualPt (S : Finset {w : InfinitePlace K // IsReal w}) (y : K) :
    polyS (realUnit K) S (dualPt K y) = ∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ) := by
  rw [polyS_realUnit]
  exact Finset.prod_congr rfl fun v _ => by rw [dualPt_fst]

section Equiv

variable (N Ndual : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  (hdual : (Ndual : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.dual ℤ ℚ (N : FractionalIdeal (𝓞 K)⁰ K))

private def dualPointEquiv :
    ↥(Ndual : FractionalIdeal (𝓞 K)⁰ K)
      ≃ ↥(LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K))
          (mixedDilLattice K (euclideanIdealLattice K N))) :=
  (idealPointEquiv K Ndual).trans
    (((ZLattice.comap_equiv ℝ (euclideanIdealLattice K Ndual) (mixedConjDilCLE K).symm.toLinearEquiv).trans
      ((LinearEquiv.ofEq _ _ (dual_euclideanIdealLattice K N Ndual hdual).symm).trans
        ((ZLattice.comap_equiv ℝ
            (LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) (euclideanIdealLattice K N))
            (mixedDilCLE K).toLinearEquiv).trans
          (LinearEquiv.ofEq _ _ (dualSubmodule_mixedDilLattice K (euclideanIdealLattice K N)).symm)))).toEquiv)

end Equiv
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTheta_DualDict
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTheta_RayBridgeEx

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real NumberField Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic IsDedekindDomain"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem le_count_span_iff_mem_pow {y : 𝓞 K} (hy : y ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    y ∈ v.asIdeal ^ k
      ↔ (k : ℤ) ≤ FractionalIdeal.count K v
          ((Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hspan0 : (Ideal.span {y} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hy
  rw [FractionalIdeal.count_coe K v hspan0]
  have hirr : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have hmk0 : Associates.mk (Ideal.span {y} : Ideal (𝓞 K)) ≠ 0 :=
    Associates.mk_ne_zero.mpr hspan0
  constructor
  · intro hmem
    have hdvd : v.asIdeal ^ k ∣ Ideal.span {y} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_le.trans Set.singleton_subset_iff).mpr hmem)
    have hmk := Associates.mk_le_mk_iff_dvd.mpr hdvd
    rw [Associates.mk_pow] at hmk
    exact_mod_cast (Associates.prime_pow_dvd_iff_le hmk0 hirr).mp hmk
  · intro hle
    have hk : k ≤ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors := by
      exact_mod_cast hle
    have hmk := (Associates.prime_pow_dvd_iff_le hmk0 hirr).mpr hk
    rw [← Associates.mk_pow] at hmk
    exact (Ideal.span_le.trans Set.singleton_subset_iff).mp
      (Ideal.le_of_dvd (Associates.mk_le_mk_iff_dvd.mp hmk))

private theorem exists_isCoprimeGenerator (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ x₀ : K, IsCoprimeGenerator K 𝔣 χ 𝔞 x₀ := by
  classical
  by_cases h𝔣' : 𝔣 = ⊤

  · subst h𝔣'
    have h𝔞0 : ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      Units.ne_zero _
    have hbot : ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K).coeToSubmodule ≠ ⊥ :=
      fun h => h𝔞0 (FractionalIdeal.coeToSubmodule_inj.mp
        (h.trans FractionalIdeal.coe_zero.symm))
    obtain ⟨x₀, hx₀mem, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hmem : x₀ ∈ ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.mem_coe.mp hx₀mem
    have hJ0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx₀0) (Units.ne_zero _)
    exact ⟨x₀, hmem,
      chiIdeal_ne_zero_of_mem χ hJ0 (mem_coprimeToModulus_top K (Units.mk0 _ hJ0))⟩

  · obtain ⟨d, 𝔟, hd0, h𝔞⟩ :=
      FractionalIdeal.exists_eq_spanSingleton_mul
        ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    have h𝔟0 : 𝔟 ≠ 0 := by
      rintro rfl
      apply Units.ne_zero 𝔞
      rw [h𝔞, Ideal.zero_eq_bot, FractionalIdeal.coeIdeal_bot, mul_zero]
    have h𝔣0 : 𝔣 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    have hfin : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔣 * 𝔟}.Finite :=
      Ideal.finite_factors (mul_ne_zero h𝔣0 h𝔟0)
    set s : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset with hsdef
    set c : HeightOneSpectrum (𝓞 K) → ℕ :=
      fun v => (Associates.mk v.asIdeal).count (Associates.mk 𝔟).factors with hcdef

    have hpick : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x : 𝓞 K,
        (v.asIdeal ∣ 𝔣 → x ∈ v.asIdeal ^ (c v) ∧ x ∉ v.asIdeal ^ (c v + 1))
          ∧ (¬ v.asIdeal ∣ 𝔣 → x = 0) := by
      intro v
      by_cases hdvd : v.asIdeal ∣ 𝔣
      · have hlt : v.asIdeal ^ (c v + 1) < v.asIdeal ^ (c v) :=
          Ideal.pow_right_strictAnti v.asIdeal v.ne_bot v.isPrime.ne_top (Nat.lt_succ_self _)
        obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
        exact ⟨x, fun _ => ⟨hx1, hx2⟩, fun h => absurd hdvd h⟩
      · exact ⟨0, fun h => absurd h hdvd, fun _ => rfl⟩
    choose xv hxv𝔣 hxv0 using hpick

    obtain ⟨y, hy⟩ := exists_forall_sub_mem_ideal
      (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) (fun v => c v + 1)
      (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
      (fun v _ w _ hvw => fun h => hvw (HeightOneSpectrum.ext h))
      (fun v => xv v.1)

    obtain ⟨mx, hmx, hlemx⟩ := Ideal.exists_le_maximal 𝔣 h𝔣'
    have hmxbot : mx ≠ ⊥ := fun h => h𝔣 (le_bot_iff.mp (h ▸ hlemx))
    set v₀ : HeightOneSpectrum (𝓞 K) := ⟨mx, hmx.isPrime, hmxbot⟩ with hv₀def
    have hv₀𝔣 : v₀.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.mpr hlemx
    have hv₀s : v₀ ∈ s := hfin.mem_toFinset.mpr (Dvd.dvd.mul_right hv₀𝔣 𝔟)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have h1 := hy v₀ hv₀s
      rw [zero_sub] at h1
      have h2 : xv v₀ ∈ v₀.asIdeal ^ (c v₀ + 1) := by
        have := neg_mem h1
        rwa [neg_neg] at this
      exact (hxv𝔣 v₀ hv₀𝔣).2 h2

    have hycount_ge : ∀ v ∈ s, (c v : ℤ) ≤ FractionalIdeal.count K v
        ((Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      intro v hv
      rw [← le_count_span_iff_mem_pow K hy0 v (c v)]
      have hsub : y - xv v ∈ v.asIdeal ^ (c v + 1) := hy v hv
      have hsplit : y = xv v + (y - xv v) := by ring
      by_cases hdvd : v.asIdeal ∣ 𝔣
      · rw [hsplit]
        exact add_mem (hxv𝔣 v hdvd).1 (Ideal.pow_le_pow_right (Nat.le_succ _) hsub)
      · rw [hxv0 v hdvd, sub_zero] at hsub
        exact Ideal.pow_le_pow_right (Nat.le_succ _) hsub
    have hycount_eq : ∀ v ∈ s, v.asIdeal ∣ 𝔣 → FractionalIdeal.count K v
        ((Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = (c v : ℤ) := by
      intro v hv hdvd
      refine le_antisymm ?_ (hycount_ge v hv)
      by_contra hgt
      rw [not_le] at hgt
      have hsucc : ((c v + 1 : ℕ) : ℤ) ≤ FractionalIdeal.count K v
          ((Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        push_cast
        omega
      have hmem := (le_count_span_iff_mem_pow K hy0 v (c v + 1)).mpr hsucc
      have hsub : y - xv v ∈ v.asIdeal ^ (c v + 1) := hy v hv
      have h2 : xv v ∈ v.asIdeal ^ (c v + 1) := by
        have hsplit : xv v = y - (y - xv v) := by ring
        rw [hsplit]
        exact sub_mem hmem hsub
      exact (hxv𝔣 v hdvd).2 h2

    have hyK0 : algebraMap (𝓞 K) K y ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hy0
    have hdK0 : algebraMap (𝓞 K) K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
    set x₀ : K := algebraMap (𝓞 K) K y * (algebraMap (𝓞 K) K d)⁻¹ with hx₀def
    have hx₀0 : x₀ ≠ 0 := mul_ne_zero hyK0 (inv_ne_zero hdK0)

    have hinv : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K d)⁻¹)
        = (((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
      refine eq_inv_of_mul_eq_one_right ?_
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hdK0,
        FractionalIdeal.spanSingleton_one]
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        = (((Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
          * (((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      rw [hx₀def, ← FractionalIdeal.spanSingleton_mul_spanSingleton, hinv,
        ← FractionalIdeal.coeIdeal_span_singleton]
    have hspany0 : ((Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
      exact hy0
    have hspand0 : ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
      exact hd0

    have hspanx₀0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx₀0
    have hJ0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      mul_ne_zero hspanx₀0 (Units.ne_zero _)
    have h𝔞inv : ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
        = (((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hJcount : ∀ v : HeightOneSpectrum (𝓞 K),
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
        = FractionalIdeal.count K v
            ((Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          - FractionalIdeal.count K v ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      intro v
      rw [FractionalIdeal.count_mul K v hspanx₀0 (Units.ne_zero _), hspan,
        FractionalIdeal.count_mul K v hspany0 (inv_ne_zero hspand0),
        FractionalIdeal.count_inv, h𝔞inv, FractionalIdeal.count_inv, h𝔞,
        FractionalIdeal.count_mul K v
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hdK0))
          (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔟0),
        hinv, FractionalIdeal.count_inv]
      ring

    have h𝔟count : ∀ v : HeightOneSpectrum (𝓞 K),
        FractionalIdeal.count K v ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = (c v : ℤ) := by
      intro v
      rw [FractionalIdeal.count_coe K v h𝔟0]
    have hcoffs : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ s → c v = 0 := by
      intro v hv
      by_contra hne
      apply hv
      rw [hsdef, hfin.mem_toFinset]
      have hdvd : v.asIdeal ∣ 𝔟 := by
        have := Associates.le_of_count_ne_zero (Associates.mk_ne_zero.mpr h𝔟0)
          v.associates_irreducible hne
        rwa [Associates.mk_le_mk_iff_dvd] at this
      exact Dvd.dvd.mul_left hdvd 𝔣

    have hJle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
      refine le_one_of_forall_count_nonneg K hJ0 fun v => ?_
      rw [hJcount v, h𝔟count v]
      by_cases hv : v ∈ s
      · linarith [hycount_ge v hv]
      · rw [hcoffs v hv]
        have := FractionalIdeal.count_coe_nonneg K v (Ideal.span {y} : Ideal (𝓞 K))
        push_cast
        linarith

    have hJc : Units.mk0 _ hJ0 ∈ coprimeToModulus K 𝔣 := by
      rw [mem_coprimeToModulus_iff K]
      intro v hdvd
      have hvs : v ∈ s := hfin.mem_toFinset.mpr (Dvd.dvd.mul_right hdvd 𝔟)
      rw [Units.val_mk0, hJcount v, h𝔟count v, hycount_eq v hvs hdvd]
      ring

    have hmem : x₀ ∈ ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← FractionalIdeal.spanSingleton_le_iff_mem]
      have h1 := mul_le_mul_left hJle
        ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      rw [one_mul] at h1
      calc FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
            * (((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
              * ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
        _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
            * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
            * ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [mul_assoc]
        _ ≤ ((𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := h1
    exact ⟨x₀, hmem, chiIdeal_ne_zero_of_mem χ hJ0 hJc⟩

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTheta_RayBridgeEx
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTheta_SeamBuild

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "NumberField NumberField.InfinitePlace Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic IsDedekindDomain"
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

private abbrev dualFI (𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K :=
  ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K)⁻¹

variable {K}
variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

section Seam

omit χ in

private theorem coeIdeal_mul_dualFI (h𝔣 : 𝔣 ≠ ⊥) :
    (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * dualFI K 𝔣 = FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h𝔣0 : (𝔣 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣
  rw [dualFI, mul_inv_rev, mul_comm ((diffFI K)⁻¹), ← mul_assoc, mul_inv_cancel₀ h𝔣0, one_mul,
    diffFI_eq_inv_dual_one, inv_inv]

omit χ in

private theorem mul_mem_dual_one (h𝔣 : 𝔣 ≠ ⊥) {y : K} (hy : y ∈ dualFI K 𝔣) {g : 𝓞 K} (hg : g ∈ 𝔣) :
    (g : K) * y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← coeIdeal_mul_dualFI h𝔣]
  exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).mpr ⟨g, hg, rfl⟩) hy

omit χ in

private theorem addChar_eq_one_of_mem_dual_one {z : K} (hz : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
    (r : 𝓞 K) : addChar K ((r : K) * z) = 1 := by
  refine addChar_eq_one_of_trace ?_
  have h := (FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)).mp hz (r : K)
    ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
  rw [Algebra.traceForm_apply, mul_comm] at h
  exact h

omit χ in

private theorem addChar_eq_one_of_mem_dualFI (h𝔣 : 𝔣 ≠ ⊥) {y : K} (hy : y ∈ dualFI K 𝔣) (g : 𝓞 K) (hg : g ∈ 𝔣) :
    addChar K ((g : K) * y) = 1 := by
  have h := addChar_eq_one_of_mem_dual_one (mul_mem_dual_one h𝔣 hy hg) 1
  rw [show (((1 : 𝓞 K) : K)) = 1 from map_one (algebraMap (𝓞 K) K), one_mul] at h
  exact h

omit χ in

private theorem datumFI_le_one_of_mem (h𝔣 : 𝔣 ≠ ⊥) {y : K} (hy : y ∈ dualFI K 𝔣) : datumFI K 𝔣 y ≤ 1 := by
  have h𝔣0 : (𝔣 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣
  have hd0 : diffFI K ≠ 0 := by
    rw [diffFI_eq_inv_dual_one]; exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)
  have hb0 : ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K) ≠ 0 := mul_ne_zero h𝔣0 hd0
  have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ y ≤ dualFI K 𝔣 := FractionalIdeal.spanSingleton_le_iff_mem.mpr hy
  calc datumFI K 𝔣 y = FractionalIdeal.spanSingleton (𝓞 K)⁰ y * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K) := by
        rw [datumFI, mul_assoc]
    _ ≤ dualFI K 𝔣 * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K) := mul_le_mul_left h1 _
    _ = 1 := inv_mul_cancel₀ hb0

private def levelIdeal (y : K) : Ideal (𝓞 K) where
  carrier := {x | (x : K) * y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [show ((a + b : 𝓞 K) : K) * y = (a : K) * y + (b : K) * y by push_cast; ring]
    exact FractionalIdeal.mem_coe.mp (Submodule.add_mem _ (FractionalIdeal.mem_coe.mpr ha) (FractionalIdeal.mem_coe.mpr hb))
  zero_mem' := by
    change ((0 : 𝓞 K) : K) * y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
    rw [show ((0 : 𝓞 K) : K) = 0 from map_zero (algebraMap (𝓞 K) K), zero_mul]
    exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
    rw [show ((c * x : 𝓞 K) : K) * y = (c : 𝓞 K) • ((x : K) * y) by rw [Algebra.smul_def]; push_cast; ring]
    exact FractionalIdeal.mem_coe.mp (Submodule.smul_mem _ c (FractionalIdeal.mem_coe.mpr hx))

omit χ in
private theorem mem_levelIdeal {y : K} {x : 𝓞 K} :
    x ∈ levelIdeal y ↔ (x : K) * y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := Iff.rfl

omit χ in
private theorem le_levelIdeal (h𝔣 : 𝔣 ≠ ⊥) {y : K} (hy : y ∈ dualFI K 𝔣) : 𝔣 ≤ levelIdeal y :=
  fun _ hg => mem_levelIdeal.mpr (mul_mem_dual_one h𝔣 hy hg)

omit χ in

private theorem levelIdeal_ne (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) {y : K} (hy : y ∈ dualFI K 𝔣)
    (hnc : ¬ ∃ h0 : datumFI K 𝔣 y ≠ 0, Units.mk0 (datumFI K 𝔣 y) h0 ∈ coprimeToModulus K 𝔣) :
    levelIdeal y ≠ 𝔣 := by
  intro heq
  by_cases hy0 : y = 0
  · apply h𝔣'
    rw [← heq, Ideal.eq_top_iff_one, mem_levelIdeal, hy0, mul_zero]
    exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
  have h𝔣0 : (𝔣 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣
  have hd0 : diffFI K ≠ 0 := by
    rw [diffFI_eq_inv_dual_one]; exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)
  have hJ0 : datumFI K 𝔣 y ≠ 0 :=
    mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0) h𝔣0) hd0

  obtain ⟨J₀, hJ₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp (datumFI_le_one_of_mem h𝔣 hy)
  have hJ₀0 : J₀ ≠ 0 := by
    rintro rfl
    exact hJ0 (by rw [← hJ₀, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot])

  have hnc' : ¬ Units.mk0 (datumFI K 𝔣 y) hJ0 ∈ coprimeToModulus K 𝔣 := fun h => hnc ⟨hJ0, h⟩
  rw [mem_coprimeToModulus_iff] at hnc'
  push Not at hnc'
  obtain ⟨v, hv, hcnt⟩ := hnc'
  rw [Units.val_mk0, ← hJ₀, FractionalIdeal.count_coe K v hJ₀0] at hcnt
  have hdvd : v.asIdeal ∣ J₀ := by
    refine (Associates.count_ne_zero_iff_dvd hJ₀0 v.irreducible).mp ?_
    exact_mod_cast hcnt
  obtain ⟨𝔮, h𝔮⟩ := hv
  have h𝔮0 : 𝔮 ≠ 0 := by
    rintro rfl
    exact h𝔣 (by rw [h𝔮, mul_zero]; rfl)
  have hnle : ¬ 𝔮 ≤ 𝔣 := by
    intro hle
    have h𝔣𝔮 : 𝔣 = 𝔮 := le_antisymm (h𝔮 ▸ Ideal.mul_le_right) hle
    have : v.asIdeal * 𝔮 = 1 * 𝔮 := by rw [← h𝔮, one_mul]; exact h𝔣𝔮
    exact v.isPrime.ne_top ((mul_right_cancel₀ h𝔮0 this).trans Ideal.one_eq_top)
  obtain ⟨x, hx𝔮, hx𝔣⟩ := SetLike.not_le_iff_exists.mp hnle
  apply hx𝔣
  rw [← heq, mem_levelIdeal]

  have hb0 : ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K) ≠ 0 := mul_ne_zero h𝔣0 hd0
  have hyJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ y = datumFI K 𝔣 y * dualFI K 𝔣 := by
    rw [dualFI, eq_mul_inv_iff_mul_eq₀ hb0, datumFI, mul_assoc]
  have hxle : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : K) * y)
      ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hyJ, ← hJ₀, ← coeIdeal_mul_dualFI h𝔣, h𝔮,
      FractionalIdeal.coeIdeal_mul, ← mul_assoc]
    refine mul_le_mul_left ?_ _
    have hx1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) ≤ (𝔮 : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.spanSingleton_le_iff_mem.mpr ((FractionalIdeal.mem_coeIdeal _).mpr ⟨x, hx𝔮, rfl⟩)
    have hJv : (J₀ : FractionalIdeal (𝓞 K)⁰ K) ≤ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr (Ideal.le_of_dvd hdvd)
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * (J₀ : FractionalIdeal (𝓞 K)⁰ K)
        ≤ (𝔮 : FractionalIdeal (𝓞 K)⁰ K) * (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := mul_le_mul' hx1 hJv
      _ = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) * (𝔮 : FractionalIdeal (𝓞 K)⁰ K) := mul_comm _ _
  exact hxle (FractionalIdeal.mem_spanSingleton_self _ _)

private theorem gaussCore_eq_zero_of_mem_dualFI (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) (S : Finset {w : InfinitePlace K // IsReal w})
    (hS : IsParity K 𝔣 χ S) (hprim : IsPrimitiveMod K 𝔣 χ) {y : K} (hy : y ∈ dualFI K 𝔣)
    (hnc : ¬ ∃ h0 : datumFI K 𝔣 y ≠ 0, Units.mk0 (datumFI K 𝔣 y) h0 ∈ coprimeToModulus K 𝔣) :
    gaussCore χ h𝔣 S y = 0 := by
  obtain ⟨α, hα0, hα1, hαpos, hαne0, hαne1⟩ :=
    hprim (levelIdeal y) (le_levelIdeal h𝔣 hy) (levelIdeal_ne h𝔣 h𝔣' hy hnc)
  change chiIdeal K 𝔣 χ (prinFI K α) ≠ 0 at hαne0
  change chiIdeal K 𝔣 χ (prinFI K α) ≠ 1 at hαne1
  have hαc : Units.mk0 (prinFI K α) (prinFI_ne_zero K hα0) ∈ coprimeToModulus K 𝔣 := by
    by_contra h
    exact hαne0 (chiIdeal_eq_zero_of_not_mem χ (prinFI_ne_zero K hα0) h)
  have h1 := gaussCore_eq_chiFin_mul χ h𝔣 h𝔣' S hS (addChar_eq_one_of_mem_dualFI h𝔣 hy) hα0 hαc

  have h2 : gaussCore χ h𝔣 S ((α : K) * y) = gaussCore χ h𝔣 S y := by
    refine gaussCore_congr χ h𝔣 S fun β => ?_
    have e : (β : K) * ((α : K) * y) = (β : K) * y + (β : K) * (((α - 1 : 𝓞 K) : K) * y) := by
      push_cast; ring
    rw [e, addChar_add, addChar_eq_one_of_mem_dual_one (mem_levelIdeal.mp hα1) β, mul_one]
  have hsgn : signAt K S (α : K) = 1 := signAt_eq_one_of_totallyPositive S hαpos
  have hchi : chiFin K 𝔣 χ S α = chiIdeal K 𝔣 χ (prinFI K α) := by
    unfold chiFin; change chiIdeal K 𝔣 χ (prinFI K α) * _ = _; rw [hsgn, mul_one]
  rw [h2, hchi] at h1
  have : (1 - chiIdeal K 𝔣 χ (prinFI K α)) * gaussCore χ h𝔣 S y = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hαne1
  · exact h

private theorem isGaussDatum_of_mem_dualFI (h𝔣 : 𝔣 ≠ ⊥) {y : K} (hy : y ∈ dualFI K 𝔣) (h0 : datumFI K 𝔣 y ≠ 0)
    (hc : Units.mk0 (datumFI K 𝔣 y) h0 ∈ coprimeToModulus K 𝔣) : IsGaussDatum K 𝔣 χ y := by
  refine ⟨?_, fun g hg => trace_mem_of_addChar_eq_one (addChar_eq_one_of_mem_dualFI h𝔣 hy g hg), ?_⟩
  · rintro rfl
    apply h0
    rw [datumFI, FractionalIdeal.spanSingleton_zero, zero_mul, zero_mul]
  · exact chiIdeal_ne_zero_of_mem χ h0 hc

private theorem gaussCore_eq_gaussSum_mul (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) (S : Finset {w : InfinitePlace K // IsReal w})
    (hS : IsParity K 𝔣 χ S) (hprim : IsPrimitiveMod K 𝔣 χ) {y₀ : K} (hy₀ : IsGaussDatum K 𝔣 χ y₀)
    {y : K} (hy : y ∈ dualFI K 𝔣) :
    gaussCore χ h𝔣 S y
      = gaussSumAt K 𝔣 χ h𝔣 S y₀ * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (datumFI K 𝔣 y)) * signAt K S y) := by
  by_cases hc : ∃ h0 : datumFI K 𝔣 y ≠ 0, Units.mk0 (datumFI K 𝔣 y) h0 ∈ coprimeToModulus K 𝔣
  · obtain ⟨h0, hc⟩ := hc
    have hyD := isGaussDatum_of_mem_dualFI χ h𝔣 hy h0 hc
    rw [gaussSumAt_indep K 𝔣 χ S hS h𝔣 hy₀ hyD, gaussSumAt_eq_mul_gaussCore]
    have hn : chiIdeal K 𝔣 χ (datumFI K 𝔣 y) * (starRingEnd ℂ) (chiIdeal K 𝔣 χ (datumFI K 𝔣 y)) = 1 := by
      rw [Complex.mul_conj, normSq_chiIdeal_of_mem χ h𝔣 h0 hc, Complex.ofReal_one]
    have hs := signAt_mul_self S hyD.1
    linear_combination (-(gaussCore χ h𝔣 S y) * (signAt K S y * signAt K S y)) * hn
      - gaussCore χ h𝔣 S y * hs
  · rw [gaussCore_eq_zero_of_mem_dualFI χ h𝔣 h𝔣' S hS hprim hy hc]
    have hz : chiIdeal K 𝔣 χ (datumFI K 𝔣 y) = 0 := by
      by_cases h0 : datumFI K 𝔣 y = 0
      · rw [h0, chiIdeal_zero]
      · exact chiIdeal_eq_zero_of_not_mem χ h0 fun h => hc ⟨h0, h⟩
    rw [hz, map_zero, zero_mul, mul_zero]

end Seam
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section General

private theorem chiIdeal_mul_of_mem_left {A : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≠ 0)
    (hAc : Units.mk0 A hA ∈ coprimeToModulus K 𝔣) (B : FractionalIdeal (𝓞 K)⁰ K) :
    chiIdeal K 𝔣 χ (A * B) = chiIdeal K 𝔣 χ A * chiIdeal K 𝔣 χ B := by
  by_cases hB : B = 0
  · rw [hB, mul_zero, chiIdeal_zero, mul_zero]
  by_cases hBc : Units.mk0 B hB ∈ coprimeToModulus K 𝔣
  · exact chiIdeal_mul_of_mem χ hA hB hAc hBc
  · have hABc : Units.mk0 (A * B) (mul_ne_zero hA hB) ∉ coprimeToModulus K 𝔣 := by
      intro h
      apply hBc
      rw [mem_coprimeToModulus_iff] at h hAc ⊢
      intro v hv
      have := h v hv
      have hAv := hAc v hv
      rw [Units.val_mk0] at hAv
      rw [Units.val_mk0, FractionalIdeal.count_mul K v hA hB, hAv, zero_add] at this
      rw [Units.val_mk0]
      exact this
    rw [chiIdeal_eq_zero_of_not_mem χ (mul_ne_zero hA hB) hABc, chiIdeal_eq_zero_of_not_mem χ hB hBc, mul_zero]

private theorem coe_rayDualIdeal (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      = ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K)⁻¹ := by
  rw [rayDualIdeal, dualIdealUnit, Units.val_mk0, FractionalIdeal.dual_eq_mul_inv, diffFI_eq_inv_dual_one,
    Units.val_mul, Units.val_mk0, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv]

private theorem mul_mem_dualFI (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x₀ : K}
    (hx₀ : x₀ ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) {y : K}
    (hy : y ∈ ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K)⁻¹) : x₀ * y ∈ dualFI K 𝔣 := by
  have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ ≤ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hx₀
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ y ≤ ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K)⁻¹ :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hy
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x₀ * y) ≤ dualFI K 𝔣 := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * FractionalIdeal.spanSingleton (𝓞 K)⁰ y
        ≤ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K)⁻¹ := mul_le_mul' h1 h2
      _ = dualFI K 𝔣 := by
        rw [dualFI, mul_inv_rev, mul_inv_rev, mul_inv_rev, show (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
          * ((diffFI K)⁻¹ * ((𝔞 : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (𝔣 : FractionalIdeal (𝓞 K)⁰ K)⁻¹))
          = ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) * ((diffFI K)⁻¹
            * (𝔣 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) by ring, mul_inv_cancel₀ 𝔞.ne_zero, one_mul]
  exact hle (FractionalIdeal.mem_spanSingleton_self _ _)

private theorem gaussCore_mul_eq_gaussSum_mul (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) (S : Finset {w : InfinitePlace K // IsReal w})
    (hS : IsParity K 𝔣 χ S) (hprim : IsPrimitiveMod K 𝔣 χ) {y₀ : K} (hy₀ : IsGaussDatum K 𝔣 χ y₀)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x₀ : K} (hx₀ : x₀ ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
    (h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)
    (hc : Units.mk0 _ h0 ∈ coprimeToModulus K 𝔣)
    {y : K} (hy : y ∈ ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K)⁻¹) :
    gaussCore χ h𝔣 S (x₀ * y)
      = gaussSumAt K 𝔣 χ h𝔣 S y₀
        * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))) * signAt K S x₀)
        * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ y
              * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S y) := by
  rw [gaussCore_eq_gaussSum_mul χ h𝔣 h𝔣' S hS hprim hy₀ (mul_mem_dualFI 𝔞 hx₀ hy)]
  have hsplit : datumFI K 𝔣 (x₀ * y)
      = (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
        * (FractionalIdeal.spanSingleton (𝓞 K)⁰ y * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K)) := by
    rw [datumFI, ← FractionalIdeal.spanSingleton_mul_spanSingleton, Units.val_inv_eq_inv_val,
      show FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)⁻¹
          * (FractionalIdeal.spanSingleton (𝓞 K)⁰ y * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * FractionalIdeal.spanSingleton (𝓞 K)⁰ y
          * (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K * ((𝔞 : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) by ring,
      inv_mul_cancel₀ 𝔞.ne_zero, mul_one]
  rw [hsplit, chiIdeal_mul_of_mem_left χ h0 hc, map_mul, signAt_mul]
  ring

private theorem absNorm_rayDualIdeal (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal.absNorm (rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
      = (|(discr K : ℝ)| * ((Ideal.absNorm 𝔣 : ℝ)
          * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ)))⁻¹ := by
  rw [rayDualIdeal, absNorm_dualIdealUnit, Units.val_mul, Units.val_mk0, map_mul, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  ring

private theorem rayScale_mul_rayScale_dual (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    rayScale K 𝔣 𝔞 * rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞) = 1 := by
  have hd : 0 < |(discr K : ℝ)| := abs_discr_pos K
  have hN : 0 < (Ideal.absNorm 𝔣 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h𝔣)
  have hA : 0 < (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := absNorm_units_pos K 𝔞
  unfold rayScale
  rw [absNorm_rayDualIdeal, ← Real.mul_rpow (by positivity) (by positivity)]
  have : |(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2
      * (|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
        * ((|(discr K : ℝ)| * ((Ideal.absNorm 𝔣 : ℝ) * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ)))⁻¹) ^ 2)
      = 1 := by
    field_simp
  rw [this, Real.one_rpow]

end General
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTheta_SeamBuild
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTheta_RayFEBuild

set_option autoImplicit false

noncomputable section

namespace M4aP2
p2m_export "M4aP2" "signAt chiIdeal IsParity chiFin IsPrimitiveMod addChar gaussSumAt IsGaussDatum"
p2m_open "M4aP2"

p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic MeasureTheory"
open scoped nonZeroDivisors Classical FourierTransform InnerProductSpace

variable (K : Type) [Field K] [NumberField K]

section Weights

variable {K}
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

private abbrev conjChar : NarrowRayClassGroup K 𝔣 →* ℂ := (starRingEnd ℂ).toMonoidHom.comp χ

private theorem chiIdeal_conjChar (I : FractionalIdeal (𝓞 K)⁰ K) :
    chiIdeal K 𝔣 (conjChar 𝔣 χ) I = (starRingEnd ℂ) (chiIdeal K 𝔣 χ I) := by
  unfold chiIdeal
  split_ifs <;> simp

variable (S : Finset {w : InfinitePlace K // IsReal w}) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem uWeight_mul_conj {x₀ : K}
    (h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)
    (hc : Units.mk0 _ h0 ∈ coprimeToModulus K 𝔣) (h𝔣 : 𝔣 ≠ ⊥) :
    uWeight K 𝔣 χ S 𝔞 x₀
      * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
          * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))) * signAt K S x₀) = 1 := by
  have hx₀ : x₀ ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero, zero_mul] at h0
    exact h0 rfl
  have hn : chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
      * (starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))) = 1 := by
    rw [Complex.mul_conj, normSq_chiIdeal_of_mem χ h𝔣 h0 hc, Complex.ofReal_one]
  have hs := signAt_mul_self S hx₀
  unfold uWeight
  linear_combination (signAt K S x₀ * signAt K S x₀) * hn + hs

end Weights
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section Constants

variable {K}

private theorem rayScale_rpow_neg_half_finrank (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    rayScale K 𝔣 𝔞 ^ (-((Module.finrank ℚ K : ℝ) / 2))
      = Real.sqrt (|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
          * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2) := by
  have hd : 0 < |(discr K : ℝ)| := abs_discr_pos K
  have hN : 0 < (Ideal.absNorm 𝔣 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h𝔣)
  have hA : 0 < (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := absNorm_units_pos K 𝔞
  have hB : 0 < |(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 := by
    positivity
  have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    positivity
  unfold rayScale
  rw [← Real.rpow_mul hB.le,
    show -(1 : ℝ) / (Module.finrank ℚ K : ℝ) * (-((Module.finrank ℚ K : ℝ) / 2)) = 1 / 2 by field_simp,
    Real.sqrt_eq_rpow]

private theorem rayFE_constants (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.sqrt (rayScale K 𝔣 𝔞) ^ k
        * ((Ideal.absNorm 𝔣 : ℝ) * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * Real.sqrt |(discr K : ℝ)|)⁻¹
        * (x / rayScale K 𝔣 𝔞) ^ k * (x / rayScale K 𝔣 𝔞) ^ ((Module.finrank ℚ K : ℝ) / 2)
      = (Real.sqrt (Ideal.absNorm 𝔣 : ℝ))⁻¹ * x ^ ((Module.finrank ℚ K : ℝ) / 2 + k)
          * Real.sqrt (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) ^ k := by
  set c := rayScale K 𝔣 𝔞 with hcdef
  have hc : 0 < c := rayScale_pos K 𝔣 h𝔣 𝔞
  have hd : 0 < |(discr K : ℝ)| := abs_discr_pos K
  have hN : 0 < (Ideal.absNorm 𝔣 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h𝔣)
  have hA : 0 < (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := absNorm_units_pos K 𝔞

  have hc' : rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞) = c⁻¹ := by
    have h := rayScale_mul_rayScale_dual (K := K) h𝔣 𝔞
    rw [← hcdef] at h
    field_simp
    linear_combination h

  have hsc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hsqrt' : Real.sqrt (c⁻¹) = (Real.sqrt c)⁻¹ := Real.sqrt_inv c
  have hsqrt0 : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'

  have hpow : (x / c) ^ ((Module.finrank ℚ K : ℝ) / 2)
      = x ^ ((Module.finrank ℚ K : ℝ) / 2) * Real.sqrt (|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
          * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2) := by
    rw [Real.div_rpow hx.le hc.le, ← rayScale_rpow_neg_half_finrank 𝔣 h𝔣 𝔞, ← hcdef, Real.rpow_neg hc.le,
      div_eq_mul_inv]
  have hsq : Real.sqrt (|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
        * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
      = Real.sqrt |(discr K : ℝ)| * Real.sqrt (Ideal.absNorm 𝔣 : ℝ)
        * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hd.le, Real.sqrt_sq hA.le]
  have hsN : Real.sqrt (Ideal.absNorm 𝔣 : ℝ) * Real.sqrt (Ideal.absNorm 𝔣 : ℝ) = (Ideal.absNorm 𝔣 : ℝ) :=
    Real.mul_self_sqrt hN.le
  have hsN0 : Real.sqrt (Ideal.absNorm 𝔣 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hsd0 : Real.sqrt |(discr K : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  rw [hc', hsqrt', hpow, hsq, Real.rpow_add hx, Real.rpow_natCast, div_pow, inv_pow]
  field_simp

  rw [show (Real.sqrt c ^ k) ^ 2 = (Real.sqrt c * Real.sqrt c) ^ k by ring, hsc,
    show Real.sqrt (Ideal.absNorm 𝔣 : ℝ) ^ 2 = (Ideal.absNorm 𝔣 : ℝ) by rw [sq, hsN]]
  ring

end Constants
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section Assembly

variable {K}
variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

omit χ in
private theorem coe_rayDualIdeal_eq_dual (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.dual ℤ ℚ ((rayModIdeal K 𝔣 𝔞 h𝔣 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := rfl

omit χ in

private theorem absNorm_rayModIdeal (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((FractionalIdeal.absNorm ((rayModIdeal K 𝔣 𝔞 h𝔣 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)
      = (Ideal.absNorm 𝔣 : ℝ) * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  rw [rayModIdeal, Units.val_mul, Units.val_mk0, map_mul, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  ring

omit χ in

private theorem coe_rayDualIdeal_inv (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (((rayDualIdeal K 𝔣 h𝔣 𝔞)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K := by
  rw [Units.val_inv_eq_inv_val, coe_rayDualIdeal, inv_inv]

private theorem phaseSum_eq_gaussCore [hF : Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) (S : Finset {w : InfinitePlace K // IsReal w}) (x₀ y : K) :
    ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a) * (𝐞 ⟪bridgeRep K 𝔣 x₀ a, dualPt K y⟫_ℝ : ℂ)
      = gaussCore χ h𝔣 S (x₀ * y) := by
  unfold gaussCore bridgeRep
  refine Finset.sum_congr ?_ fun a _ => ?_
  · congr 1
    exact Subsingleton.elim _ _
  rw [fourierChar_inner_dil_dualPt, show x₀ * ((Quotient.out a : 𝓞 K) : K) * y = ((Quotient.out a : 𝓞 K) : K) * (x₀ * y) by ring]

end Assembly
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section Frozen

variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

end Frozen
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end M4aP2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTheta_RayFEBuild
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_RayFoldInvBody

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
p2m_open "MeasureTheory Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
open scoped nonZeroDivisors Classical Real FourierTransform InnerProductSpace

variable (K : Type) [Field K] [NumberField K]

private theorem polyS_placeScale (S : Finset {w : InfinitePlace K // IsReal w})
    (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
    (z : euclidean.mixedSpace K) :
    polyS (realUnit K) S (placeScale K c hc z)
      = ((∏ v ∈ S, c v.1 : ℝ) : ℂ) * polyS (realUnit K) S z := by
  unfold polyS
  rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [inner_realUnit, inner_realUnit, placeScale_apply_fst, Complex.ofReal_mul]

private def rayDilForm (t : realSpace K) (u : euclidean.mixedSpace K) : ℝ :=
  (∑ w : {w : InfinitePlace K // IsReal w}, t w.1 * (u.fst w) ^ 2)
    + ∑ w : {w : InfinitePlace K // IsComplex w}, t w.1 * Complex.normSq (u.snd w)

private theorem rayDilForm_dilEmbed (t : realSpace K) (y : K) :
    rayDilForm K t (M4aP2.dilEmbed K y) = torusForm K t (mixedEmbedding K y) := by
  rw [rayDilForm, torusForm, sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, normAtPlace_apply_of_isReal w.2, Nat.cast_one, one_mul, Real.norm_eq_abs,
      sq_abs]
    show t w.1 * ((M4aP2.dilEmbed K y).fst w) ^ 2 = _
    rw [M4aP2.dilEmbed, mixedDil_apply_fst, Deep.Analytic.toMixed_symm_fst, mixedEmbedding_apply_isReal]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, Nat.cast_ofNat, Complex.sq_norm]
    show t w.1 * Complex.normSq ((M4aP2.dilEmbed K y).snd w) = _
    rw [M4aP2.dilEmbed, mixedDil_apply_snd, Deep.Analytic.toMixed_symm_snd, mixedEmbedding_apply_isComplex,
      Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring

private theorem rayDilForm_dualPt (t : realSpace K) (y : K) :
    rayDilForm K t (M4aP2.dualPt K y) = torusForm K t (mixedEmbedding K y) := by
  have hD : mixedDil K (M4aP2.dualPt K y)
      = mixedConjDil K ((euclidean.toMixed K).symm (mixedEmbedding K y)) := by
    rw [M4aP2.dualPt]
    exact LinearEquiv.apply_symm_apply _ _
  rw [rayDilForm, torusForm, sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, normAtPlace_apply_of_isReal w.2, Nat.cast_one, one_mul, Real.norm_eq_abs,
      sq_abs, M4aP2.dualPt_fst, mixedEmbedding_apply_isReal]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, Nat.cast_ofNat, Complex.sq_norm]
    have h1 : ((Real.sqrt 2 : ℝ) : ℂ) * (M4aP2.dualPt K y).snd w
        = 2 * (starRingEnd ℂ) (((euclidean.toMixed K).symm (mixedEmbedding K y)).snd w) := by
      rw [← mixedDil_apply_snd, hD, mixedConjDil_apply_snd]
    have h2 := congrArg Complex.normSq h1
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2), Complex.normSq_conj] at h2
    have h3 : Complex.normSq ((M4aP2.dualPt K y).snd w)
        = 2 * Complex.normSq (((euclidean.toMixed K).symm (mixedEmbedding K y)).snd w) := by
      have h4 : Complex.normSq (2 : ℂ) = 4 := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.normSq_ofReal]; norm_num
      rw [h4] at h2; linarith
    rw [h3, Deep.Analytic.toMixed_symm_snd, mixedEmbedding_apply_isComplex]
    ring

private def rayFlatScaleVec (c : ℝ) (t : realSpace K) : InfinitePlace K → ℝ :=
  fun w => Real.sqrt (c * t w)

omit [NumberField K] in
private theorem rayFlatScaleVec_pos {c : ℝ} (hc : 0 < c) {t : realSpace K} (ht : ∀ w, 0 < t w)
    (w : InfinitePlace K) : 0 < rayFlatScaleVec K c t w :=
  Real.sqrt_pos.mpr (by have := ht w; positivity)

omit [NumberField K] in
private theorem rayFlatScaleVec_sq {c : ℝ} (hc : 0 < c) {t : realSpace K} (ht : ∀ w, 0 < t w)
    (w : InfinitePlace K) : rayFlatScaleVec K c t w ^ 2 = c * t w :=
  Real.sq_sqrt (by have := ht w; positivity)

private theorem norm_sq_placeScale_rayFlatScaleVec {c : ℝ} (hc : 0 < c) {t : realSpace K}
    (ht : ∀ w, 0 < t w) (u : euclidean.mixedSpace K) :
    ‖placeScale K (rayFlatScaleVec K c t) (rayFlatScaleVec_pos K hc ht) u‖ ^ 2
      = c * rayDilForm K t u := by
  rw [norm_sq_eq_sum, rayDilForm, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [placeScale_apply_fst, mul_pow, rayFlatScaleVec_sq K hc ht]
    ring
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [placeScale_apply_snd, Complex.normSq_mul, Complex.normSq_ofReal,
      show rayFlatScaleVec K c t w.1 * rayFlatScaleVec K c t w.1 = c * t w.1 by
        rw [← pow_two]; exact rayFlatScaleVec_sq K hc ht w.1]
    ring

private theorem norm_sq_placeScale_symm_rayFlatScaleVec {c : ℝ} (hc : 0 < c) {t : realSpace K}
    (ht : ∀ w, 0 < t w) (u : euclidean.mixedSpace K) :
    ‖(placeScale K (rayFlatScaleVec K c t) (rayFlatScaleVec_pos K hc ht)).symm u‖ ^ 2
      = (1 / c) * rayDilForm K t⁻¹ u := by
  rw [norm_sq_eq_sum, rayDilForm, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    have h1 : t v.1 ≠ 0 := (ht v.1).ne'
    have h2 : c ≠ 0 := hc.ne'
    rw [placeScale_symm_apply_fst, div_pow,
      show rayFlatScaleVec K c t v.1 ^ 2 = c * t v.1 from rayFlatScaleVec_sq K hc ht v.1,
      Pi.inv_apply]
    field_simp
  · refine Finset.sum_congr rfl fun w _ => ?_
    have h1 : t w.1 ≠ 0 := (ht w.1).ne'
    have h2 : c ≠ 0 := hc.ne'
    rw [placeScale_symm_apply_snd, map_div₀, Complex.normSq_ofReal,
      show rayFlatScaleVec K c t w.1 * rayFlatScaleVec K c t w.1 = c * t w.1 by
        rw [← pow_two]; exact rayFlatScaleVec_sq K hc ht w.1,
      Pi.inv_apply]
    field_simp

private theorem polyS_realUnit_placeScale_symm (S : Finset {w : InfinitePlace K // IsReal w})
    (cv : InfinitePlace K → ℝ) (hcv : ∀ w, 0 < cv w) (z : euclidean.mixedSpace K) :
    polyS (realUnit K) S ((placeScale K cv hcv).symm z)
      = ((((∏ v ∈ S, cv v.1)⁻¹ : ℝ)) : ℂ) * polyS (realUnit K) S z := by
  rw [polyS_realUnit, polyS_realUnit,
    show (((((∏ v ∈ S, cv v.1)⁻¹ : ℝ)) : ℂ)) = ∏ v ∈ S, (((cv v.1)⁻¹ : ℝ) : ℂ) by
      rw [← Finset.prod_inv_distrib, Complex.ofReal_prod],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [placeScale_symm_apply_fst]
  push_cast
  ring

private theorem polyS_realUnit_dilEmbed (S : Finset {w : InfinitePlace K // IsReal w}) (y : K) :
    polyS (realUnit K) S (dilEmbed K y) = ∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ) := by
  rw [polyS_realUnit]
  exact Finset.prod_congr rfl fun v _ => by rw [dilEmbed_fst]

variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem rayFoldSummand_eq_dil (c : ℝ) (t' : realSpace K) (x : K) :
    rayFoldSummand K 𝔣 χ S 𝔞 c t' x
      = uWeight K 𝔣 χ S 𝔞 x
          * (polyS (realUnit K) S (dilEmbed K x)
            * ((Real.exp (-π * c * rayDilForm K t' (dilEmbed K x)) : ℝ) : ℂ)) := by
  rw [rayFoldSummand, polyS_realUnit_dilEmbed, rayDilForm_dilEmbed, mul_assoc]

private theorem tsum_rayFoldSummand_eq_coset [Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
    (hP : IsParity K 𝔣 χ S) {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀)
    (c : ℝ) (t' : realSpace K)
    (hsum : Summable fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      rayFoldSummand K 𝔣 χ S 𝔞 c t' (x : K)) :
    (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t' (x : K))
      = uWeight K 𝔣 χ S 𝔞 x₀
          * ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)
              * ∑' v : dilRayLattice K 𝔣 𝔞 h𝔣,
                  polyS (realUnit K) S ((v : euclidean.mixedSpace K) + bridgeRep K 𝔣 x₀ a)
                    * ((Real.exp (-π * c * rayDilForm K t'
                        ((v : euclidean.mixedSpace K) + bridgeRep K 𝔣 x₀ a)) : ℝ) : ℂ) := by
  classical
  haveI : Fintype (↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ⧸ raySub K 𝔣 𝔞) :=
    Fintype.ofEquiv _ (cosetIndexEquiv K 𝔣 χ 𝔞 h𝔣 hx₀)
  set e₀ : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      ≃ ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
    Equiv.subtypeEquivRight fun x => FractionalIdeal.mem_coe with he₀
  set f : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) → ℂ := fun y =>
    rayFoldSummand K 𝔣 χ S 𝔞 c t' (y : K) with hfdef
  have hsum' : Summable f := (Equiv.summable_iff e₀).mpr hsum
  have h1 : (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t' (x : K))
      = ∑' y, f y :=
    (Equiv.tsum_eq e₀ _).symm
  have h2 : (∑' y, f y)
      = ∑ a : 𝓞 K ⧸ 𝔣, ∑' v : ((QuotientAddGroup.mk (s := raySub K 𝔣 𝔞)) ⁻¹'
          {QuotientAddGroup.mk (s := raySub K 𝔣 𝔞) (genPoint K 𝔣 χ 𝔞 hx₀ a)} :
            Set ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)), f v := by
    rw [tsum_partition_quotient (H := raySub K 𝔣 𝔞) hsum', tsum_fintype]
    exact (Fintype.sum_equiv (cosetIndexEquiv K 𝔣 χ 𝔞 h𝔣 hx₀)
      (fun a => ∑' v : ((QuotientAddGroup.mk (s := raySub K 𝔣 𝔞)) ⁻¹'
          {QuotientAddGroup.mk (s := raySub K 𝔣 𝔞) (genPoint K 𝔣 χ 𝔞 hx₀ a)} :
            Set ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)), f v)
      (fun c' => ∑' v : ((QuotientAddGroup.mk (s := raySub K 𝔣 𝔞)) ⁻¹' {c'} :
            Set ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)), f v)
      (fun a => rfl)).symm
  have h3 : ∀ a : 𝓞 K ⧸ 𝔣,
      (∑' v : ((QuotientAddGroup.mk (s := raySub K 𝔣 𝔞)) ⁻¹'
          {QuotientAddGroup.mk (s := raySub K 𝔣 𝔞) (genPoint K 𝔣 χ 𝔞 hx₀ a)} :
            Set ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)), f v)
        = chiFin K 𝔣 χ S (Quotient.out a) * uWeight K 𝔣 χ S 𝔞 x₀
            * ∑' v : dilRayLattice K 𝔣 𝔞 h𝔣,
                polyS (realUnit K) S ((v : euclidean.mixedSpace K) + bridgeRep K 𝔣 x₀ a)
                  * ((Real.exp (-π * c * rayDilForm K t'
                      ((v : euclidean.mixedSpace K) + bridgeRep K 𝔣 x₀ a)) : ℝ) : ℂ) := by
    intro a
    rw [tsum_fiber_eq_tsum_translate (H := raySub K 𝔣 𝔞) _ (genPoint K 𝔣 χ 𝔞 hx₀ a) rfl]
    set G : euclidean.mixedSpace K → ℂ := fun w =>
      polyS (realUnit K) S (w + bridgeRep K 𝔣 x₀ a)
        * ((Real.exp (-π * c * rayDilForm K t' (w + bridgeRep K 𝔣 x₀ a)) : ℝ) : ℂ) with hGdef
    have hcongr : ∀ u : ↥(raySub K 𝔣 𝔞),
        f ((u : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
            + genPoint K 𝔣 χ 𝔞 hx₀ a)
          = (chiFin K 𝔣 χ S (Quotient.out a) * uWeight K 𝔣 χ S 𝔞 x₀)
              * G (((raySubLatticeEquiv K 𝔣 𝔞 h𝔣) u : euclidean.mixedSpace K)) := by
      intro u
      have huval : ((u : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) : K)
          ∈ (𝔣 : FractionalIdeal (𝓞 K)⁰ K) * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := u.2
      have hval : ((((u : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
          + genPoint K 𝔣 χ 𝔞 hx₀ a :
          ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))) : K)
          = x₀ * ((Quotient.out a : 𝓞 K) : K)
            + ((u : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) : K) := by
        push_cast [genPoint]
        ring
      have hequiv : ((raySubLatticeEquiv K 𝔣 𝔞 h𝔣) u : euclidean.mixedSpace K)
          = dilEmbed K ((u : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) : K) := rfl
      have hpt : dilEmbed K (x₀ * ((Quotient.out a : 𝓞 K) : K)
            + ((u : ↥((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) : K))
          = ((raySubLatticeEquiv K 𝔣 𝔞 h𝔣) u : euclidean.mixedSpace K)
              + bridgeRep K 𝔣 x₀ a := by
        rw [dilEmbed_add, bridgeRep_eq_dilEmbed, hequiv, add_comm]
      show rayFoldSummand K 𝔣 χ S 𝔞 c t' _ = _
      rw [rayFoldSummand_eq_dil K 𝔣 χ S 𝔞 c t' _, hval,
        uWeight_add_mem K 𝔣 χ S 𝔞 h𝔣 h𝔣' hP hx₀ (Quotient.out a) huval, hpt, hGdef]
    rw [tsum_congr hcongr, tsum_mul_left]
    have htr : (∑' u : ↥(raySub K 𝔣 𝔞),
          G (((raySubLatticeEquiv K 𝔣 𝔞 h𝔣) u : euclidean.mixedSpace K)))
        = ∑' v : ↥(dilRayLattice K 𝔣 𝔞 h𝔣), G (v : euclidean.mixedSpace K) :=
      Equiv.tsum_eq (raySubLatticeEquiv K 𝔣 𝔞 h𝔣) (fun v => G (v : euclidean.mixedSpace K))
    rw [htr, hGdef]
  rw [h1, h2]
  simp only [h3]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

private theorem tsum_dil_eq_scaled_oddGaussian (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) (r : euclidean.mixedSpace K) :
    (∑' v : dilRayLattice K 𝔣 𝔞 h𝔣,
        polyS (realUnit K) S ((v : euclidean.mixedSpace K) + r)
          * ((Real.exp (-π * c * rayDilForm K t'
              ((v : euclidean.mixedSpace K) + r)) : ℝ) : ℂ))
      = ((((∏ v ∈ S, rayFlatScaleVec K c t' v.1 : ℝ))⁻¹ : ℝ) : ℂ)
          * ∑' v' : scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
                (dilRayLattice K 𝔣 𝔞 h𝔣),
              oddGaussian (realUnit K) 1 S ((v' : euclidean.mixedSpace K)
                + placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht') r) := by
  rw [← tsum_mul_left]
  rw [← Equiv.tsum_eq ((ZLattice.comap_equiv ℝ (dilRayLattice K 𝔣 𝔞 h𝔣)
      (placeScale K (rayFlatScaleVec K c t')
        (rayFlatScaleVec_pos K hc ht')).toContinuousLinearEquiv.symm.toLinearEquiv).toEquiv)
      (fun v' => ((((∏ v ∈ S, rayFlatScaleVec K c t' v.1 : ℝ))⁻¹ : ℝ) : ℂ)
        * oddGaussian (realUnit K) 1 S ((v' : euclidean.mixedSpace K)
            + placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht') r))]
  refine tsum_congr fun v => ?_
  have hco : ((((ZLattice.comap_equiv ℝ (dilRayLattice K 𝔣 𝔞 h𝔣)
      (placeScale K (rayFlatScaleVec K c t')
        (rayFlatScaleVec_pos K hc ht')).toContinuousLinearEquiv.symm.toLinearEquiv).toEquiv v) :
        _) : euclidean.mixedSpace K)
      = placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
          (v : euclidean.mixedSpace K) := rfl
  rw [hco, ← map_add, oddGaussian, gaussianMap_apply,
    show ‖placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
        ((v : euclidean.mixedSpace K) + r)‖ ^ 2
      = c * rayDilForm K t' ((v : euclidean.mixedSpace K) + r) from
      norm_sq_placeScale_rayFlatScaleVec K hc ht' _,
    polyS_placeScale K S (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')]
  have hne : ((∏ v ∈ S, rayFlatScaleVec K c t' v.1 : ℝ)) ≠ 0 :=
    (Finset.prod_pos fun v _ => rayFlatScaleVec_pos K hc ht' v.1).ne'
  have hπ : -π * 1 * (c * rayDilForm K t' ((v : euclidean.mixedSpace K) + r))
      = -π * c * rayDilForm K t' ((v : euclidean.mixedSpace K) + r) := by ring
  rw [hπ]
  have hneC : ((∏ v ∈ S, rayFlatScaleVec K c t' v.1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hne
  push_cast
  field_simp
  have hneC' : (∏ i ∈ S, ((rayFlatScaleVec K c t' i.1 : ℝ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Complex.ofReal_ne_zero.mpr (rayFlatScaleVec_pos K hc ht' i.1).ne'
  rw [mul_div_assoc, div_self hneC', mul_one]

private theorem prod_rayFlatScaleVec_pow_mult {c : ℝ} (hc : 0 < c) {t' : realSpace K}
    (ht' : ∀ w, 0 < t' w) :
    (∏ w : InfinitePlace K, rayFlatScaleVec K c t' w ^ mult w)
      = Real.sqrt (c ^ (Module.finrank ℚ K) * torusNorm K t') := by
  have hsq : (∏ w : InfinitePlace K, rayFlatScaleVec K c t' w ^ mult w) ^ 2
      = c ^ (Module.finrank ℚ K) * torusNorm K t' := by
    rw [← Finset.prod_pow]
    have h1 : ∀ w : InfinitePlace K, (rayFlatScaleVec K c t' w ^ mult w) ^ 2
        = (c * t' w) ^ mult w := fun w => by
      rw [← pow_mul, mul_comm (mult w) 2, pow_mul, rayFlatScaleVec_sq K hc ht']
    rw [Finset.prod_congr rfl fun w _ => h1 w]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, torusNorm]
    rw [sum_mult_eq]
  have hnn : 0 ≤ ∏ w : InfinitePlace K, rayFlatScaleVec K c t' w ^ mult w :=
    Finset.prod_nonneg fun w _ => pow_nonneg (Real.sqrt_nonneg _) _
  rw [← hsq, Real.sqrt_sq hnn]

private theorem gaussFT_zero_eq_inv_sqrt_pow {c : ℝ} (hc : 0 < c) :
    gaussFT c (0 : euclidean.mixedSpace K)
      = (((Real.sqrt (c ^ (Module.finrank ℚ K)))⁻¹ : ℝ) : ℂ) := by
  unfold gaussFT
  rw [NumberField.mixedEmbedding.euclidean.finrank, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one]
  have h1 : (1 / (c : ℂ)) = (((c⁻¹ : ℝ)) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_natCast, show ((Module.finrank ℚ K : ℝ) : ℂ) / 2
      = (((Module.finrank ℚ K : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ c⁻¹)]
  congr 1
  rw [Real.inv_rpow hc.le]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast c (Module.finrank ℚ K), ← Real.rpow_mul hc.le,
    show (Module.finrank ℚ K : ℝ) * (1 / 2) = (Module.finrank ℚ K : ℝ) / 2 by ring]

private theorem inf_mul_heckeForm_le_torusForm {t' : realSpace K} (_ht' : ∀ w, 0 < t' w) (x : K) :
    (Finset.univ.inf' Finset.univ_nonempty t') * heckeForm K x
      ≤ torusForm K t' (mixedEmbedding K x) := by
  have hm : ∀ w : InfinitePlace K, Finset.univ.inf' Finset.univ_nonempty t' ≤ t' w :=
    fun w => Finset.inf'_le _ (Finset.mem_univ w)
  have hh : (Finset.univ.inf' Finset.univ_nonempty t') * heckeForm K x
      = ∑ w : InfinitePlace K, (mult w : ℝ) * (Finset.univ.inf' Finset.univ_nonempty t')
          * normAtPlace w (mixedEmbedding K x) ^ 2 := by
    rw [heckeForm, mul_add, Finset.mul_sum, Finset.mul_sum, sum_eq_sum_add_sum]
    congr 1
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [mult_isReal, normAtPlace_apply, Nat.cast_one]
      ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [mult_isComplex, normAtPlace_apply, Nat.cast_ofNat]
      ring
  rw [hh, torusForm]
  refine Finset.sum_le_sum fun w _ => ?_
  have h1 : (0 : ℝ) ≤ (mult w : ℝ) * normAtPlace w (mixedEmbedding K x) ^ 2 := by positivity
  calc (mult w : ℝ) * (Finset.univ.inf' Finset.univ_nonempty t')
        * normAtPlace w (mixedEmbedding K x) ^ 2
      = ((mult w : ℝ) * normAtPlace w (mixedEmbedding K x) ^ 2)
          * Finset.univ.inf' Finset.univ_nonempty t' := by ring
    _ ≤ ((mult w : ℝ) * normAtPlace w (mixedEmbedding K x) ^ 2) * t' w :=
        mul_le_mul_of_nonneg_left (hm w) h1
    _ = (mult w : ℝ) * t' w * normAtPlace w (mixedEmbedding K x) ^ 2 := by ring

private theorem norm_uWeight_le_norm_rayWeight (h𝔣' : 𝔣 ≠ ⊤) (x : K) :
    ‖uWeight K 𝔣 χ S 𝔞 x‖ ≤ ‖rayWeight K 𝔣 χ 𝔞 x‖ := by
  by_cases hx : x = 0
  · subst hx
    rw [uWeight, rayWeight, if_pos rfl, if_neg h𝔣', FractionalIdeal.spanSingleton_zero,
      zero_mul, chiIdeal_zero, zero_mul, norm_zero]
  · rw [uWeight, rayWeight, if_neg hx, norm_mul]
    by_cases hs : signAt K S x = 0
    · rw [hs, norm_zero, mul_zero]
      exact norm_nonneg _
    · have h1 : ‖signAt K S x‖ = 1 := by
        have h := normSq_signAt (K := K) S hx
        rw [Complex.normSq_eq_norm_sq] at h
        nlinarith [norm_nonneg (signAt K S x)]
      rw [h1, mul_one]

private theorem rayFoldSummand_summable (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) :
    Summable fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      rayFoldSummand K 𝔣 χ S 𝔞 c t' (x : K) := by
  classical
  set m := Finset.univ.inf' Finset.univ_nonempty t' with hmdef
  have hm : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff]
    exact fun w _ => ht' w
  have hrs : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  have ht₀ : 0 < c * m / rayScale K 𝔣 𝔞 := by positivity
  have hdiag : Summable fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      ‖rayWeight K 𝔣 χ 𝔞 (x : K)
        * (((∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K))
            * Real.exp (-π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞)
                * heckeForm K (x : K)) : ℝ) : ℂ)‖ :=
    summable_norm_iff.mpr (raySummand_summable K 𝔣 χ S 𝔞 h𝔣 ht₀)
  refine Summable.of_norm_bounded
    (g := fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ : ℝ) ^ S.card
        * ‖rayWeight K 𝔣 χ 𝔞 (x : K)
            * (((∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K))
                * Real.exp (-π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞)
                    * heckeForm K (x : K)) : ℝ) : ℂ)‖)
    (hdiag.mul_left _) ?_
  intro x
  have hexp : Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))
      ≤ Real.exp (-π * c * (m * heckeForm K (x : K))) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 := inf_mul_heckeForm_le_torusForm K ht' (x : K)
    rw [← hmdef] at h1
    have h2 : (0 : ℝ) < π * c := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2.le
    nlinarith [h3]
  rw [rayFoldSummand, norm_mul, norm_mul]
  have hnp : ‖(∏ v ∈ S, ((embedding_of_isReal v.2 (x : K) : ℝ) : ℂ))‖
      = ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K) := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun v _ => by
      rw [Complex.norm_real, norm_embedding_of_isReal]
  have hge : ‖(((Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))) : ℝ) : ℂ)‖
      = Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K))) := by
    rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  have hrw : ‖(((∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K))
        * Real.exp (-π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞)
            * heckeForm K (x : K)) : ℝ) : ℂ)‖
      = (Real.sqrt (rayScale K 𝔣 𝔞) ^ S.card * ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
          * Real.exp (-π * c * (m * heckeForm K (x : K))) := by
    have hprodnn : (0 : ℝ) ≤ ∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K) :=
      Finset.prod_nonneg fun v _ => mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp,
      abs_of_nonneg hprodnn, Finset.prod_mul_distrib, Finset.prod_const,
      show -π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞) * heckeForm K (x : K)
          = -π * c * (m * heckeForm K (x : K)) by field_simp; try ring]
  rw [hnp, hge, norm_mul, hrw]
  have hu := norm_uWeight_le_norm_rayWeight K 𝔣 χ S 𝔞 h𝔣' (x : K)
  have hprodnn2 : (0:ℝ) ≤ ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K) :=
    Finset.prod_nonneg fun v _ => apply_nonneg _ _
  have hsrs0 : Real.sqrt (rayScale K 𝔣 𝔞) ≠ 0 := (Real.sqrt_pos.mpr hrs).ne'
  have hgoal : ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ : ℝ) ^ S.card
      * (‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
        * ((Real.sqrt (rayScale K 𝔣 𝔞) ^ S.card * ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * (m * heckeForm K (x : K)))))
      = ‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
          * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * (m * heckeForm K (x : K)))) := by
    rw [show ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ : ℝ) ^ S.card
        * (‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
          * ((Real.sqrt (rayScale K 𝔣 𝔞) ^ S.card * ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
              * Real.exp (-π * c * (m * heckeForm K (x : K)))))
        = ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ * Real.sqrt (rayScale K 𝔣 𝔞)) ^ S.card
            * (‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
              * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
                * Real.exp (-π * c * (m * heckeForm K (x : K))))) by rw [mul_pow]; ring,
      inv_mul_cancel₀ hsrs0, one_pow, one_mul]
  rw [hgoal]
  calc ‖uWeight K 𝔣 χ S 𝔞 (x : K)‖ * (∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
        * Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))
      = ‖uWeight K 𝔣 χ S 𝔞 (x : K)‖
          * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))) := by ring
    _ ≤ ‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
          * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * (m * heckeForm K (x : K)))) :=
        mul_le_mul hu (mul_le_mul_of_nonneg_left hexp hprodnn2) (by positivity) (norm_nonneg _)

private noncomputable def rayDualTransportEquiv (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) :
    ↥((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      ≃ ↥(LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K))
          (scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
            (mixedDilLattice K (euclideanIdealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣))))) :=
  (dualPointEquiv K (rayModIdeal K 𝔣 𝔞 h𝔣) (rayDualIdeal K 𝔣 h𝔣 𝔞)
      (coe_rayDualIdeal_eq_dual h𝔣 𝔞)).trans
    (((ZLattice.comap_equiv ℝ
        (LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K))
          (mixedDilLattice K (euclideanIdealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣))))
        (placeScale K (rayFlatScaleVec K c t')
          (rayFlatScaleVec_pos K hc ht')).toContinuousLinearEquiv.toLinearEquiv).toEquiv).trans
      (LinearEquiv.ofEq _ _
        (dualSubmodule_scaleLattice K (rayFlatScaleVec K c t')
          (rayFlatScaleVec_pos K hc ht')
          (mixedDilLattice K (euclideanIdealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣)))).symm).toEquiv)

private theorem rayDualTransportEquiv_apply (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w)
    (z : ↥((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
        : FractionalIdeal (𝓞 K)⁰ K)) :
    ((rayDualTransportEquiv K 𝔣 𝔞 h𝔣 hc ht' z : _) : euclidean.mixedSpace K)
      = (placeScale K (rayFlatScaleVec K c t')
          (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)) := rfl

private theorem scaled_coset_poisson_dual [Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) (x₀ : K) :
    (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)
        * ∑' v' : scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
              (dilRayLattice K 𝔣 𝔞 h𝔣),
            oddGaussian (realUnit K) 1 S ((v' : euclidean.mixedSpace K)
              + placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
                  (bridgeRep K 𝔣 x₀ a)))
      = (ZLattice.covolume (scaleLattice K (rayFlatScaleVec K c t')
            (rayFlatScaleVec_pos K hc ht') (dilRayLattice K 𝔣 𝔞 h𝔣)) volume : ℂ)⁻¹
          * (-Complex.I) ^ S.card
          * ∑' z : ↥((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
                : FractionalIdeal (𝓞 K)⁰ K),
              gaussCore χ h𝔣 S (x₀ * (z : K))
                * (polyS (realUnit K) S
                    ((placeScale K (rayFlatScaleVec K c t')
                        (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)))
                  * gaussFT 1
                      ((placeScale K (rayFlatScaleVec K c t')
                          (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)))) := by
  classical
  haveI : DiscreteTopology (dilRayLattice K 𝔣 𝔞 h𝔣) :=
    inferInstanceAs (DiscreteTopology (dilLattice K (rayModIdeal K 𝔣 𝔞 h𝔣)))
  haveI : IsZLattice ℝ (dilRayLattice K 𝔣 𝔞 h𝔣) :=
    inferInstanceAs (IsZLattice ℝ (dilLattice K (rayModIdeal K 𝔣 𝔞 h𝔣)))
  rw [weightedOddCoset_poisson (realUnit K)
      (scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
        (dilRayLattice K 𝔣 𝔞 h𝔣))
      (orthonormal_realUnit K)
      (fun a : 𝓞 K ⧸ 𝔣 => placeScale K (rayFlatScaleVec K c t')
        (rayFlatScaleVec_pos K hc ht') (bridgeRep K 𝔣 x₀ a))
      (fun a : 𝓞 K ⧸ 𝔣 => chiFin K 𝔣 χ S (Quotient.out a)) one_pos S]
  rw [show (1 / ((1 : ℝ) : ℂ)) ^ S.card = 1 by norm_num, mul_one]
  congr 1
  refine ((Equiv.tsum_eq (rayDualTransportEquiv K 𝔣 𝔞 h𝔣 hc ht') _).symm).trans
    (tsum_congr fun z => ?_)
  rw [rayDualTransportEquiv_apply K 𝔣 𝔞 h𝔣 hc ht' z]
  have hphase : (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)
      * ((𝐞 ⟪placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
            (bridgeRep K 𝔣 x₀ a),
          (placeScale K (rayFlatScaleVec K c t')
            (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K))⟫_ℝ : Circle) : ℂ))
      = gaussCore χ h𝔣 S (x₀ * (z : K)) := by
    rw [← phaseSum_eq_gaussCore χ h𝔣 S x₀ (z : K)]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    rw [inner_placeScale, LinearEquiv.apply_symm_apply]
  rw [hphase]

private theorem gaussCore_zero [Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) :
    gaussCore χ h𝔣 S (0 : K) = ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a) := by
  unfold gaussCore
  refine Finset.sum_congr ?_ fun a _ => ?_
  · congr 1
    exact Subsingleton.elim _ _
  · rw [mul_zero, addChar_eq_one_of_trace (by simp), mul_one]

private theorem gaussFT_one_placeScale_symm_flat {c : ℝ} (hc : 0 < c) {t' : realSpace K}
    (ht' : ∀ w, 0 < t' w) (u : euclidean.mixedSpace K) :
    gaussFT 1 ((placeScale K (rayFlatScaleVec K c t')
        (rayFlatScaleVec_pos K hc ht')).symm u)
      = ((Real.exp (-π * (1 / c) * rayDilForm K t'⁻¹ u) : ℝ) : ℂ) := by
  unfold gaussFT
  rw [Complex.ofReal_one, one_div, inv_one, Complex.one_cpow, one_mul, div_one,
    show ((‖(placeScale K (rayFlatScaleVec K c t')
        (rayFlatScaleVec_pos K hc ht')).symm u‖ : ℂ)) ^ 2
      = (((‖(placeScale K (rayFlatScaleVec K c t')
          (rayFlatScaleVec_pos K hc ht')).symm u‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    norm_sq_placeScale_symm_rayFlatScaleVec K hc ht' u, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem summable_ray_dual_series [Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) (x₀ : K) :
    Summable fun z : ↥((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
        : FractionalIdeal (𝓞 K)⁰ K) =>
      gaussCore χ h𝔣 S (x₀ * (z : K))
        * (polyS (realUnit K) S
            ((placeScale K (rayFlatScaleVec K c t')
                (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)))
          * gaussFT 1
              ((placeScale K (rayFlatScaleVec K c t')
                  (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)))) := by
  classical
  have hph : ∀ a : 𝓞 K ⧸ 𝔣, Summable fun m :
      ↥(LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K))
        (scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
          (mixedDilLattice K (euclideanIdealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣))))) =>
      chiFin K 𝔣 χ S (Quotient.out a)
        * ((𝐞 ⟪placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
              (bridgeRep K 𝔣 x₀ a), (m : euclidean.mixedSpace K)⟫_ℝ : Circle) : ℂ)
        * (polyS (realUnit K) S (m : euclidean.mixedSpace K)
          * gaussFT 1 (m : euclidean.mixedSpace K)) := by
    intro a
    have h := (phase_oddGaussian_summable (realUnit K)
        (scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
          (mixedDilLattice K (euclideanIdealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣))))
        (orthonormal_realUnit K)
        (placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
          (bridgeRep K 𝔣 x₀ a)) one_pos S).mul_left (chiFin K 𝔣 χ S (Quotient.out a))
    exact h.congr fun m => by ring
  have hsum : Summable fun m :
      ↥(LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K))
        (scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
          (mixedDilLattice K (euclideanIdealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣))))) =>
      (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)
          * ((𝐞 ⟪placeScale K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
                (bridgeRep K 𝔣 x₀ a), (m : euclidean.mixedSpace K)⟫_ℝ : Circle) : ℂ))
        * (polyS (realUnit K) S (m : euclidean.mixedSpace K)
          * gaussFT 1 (m : euclidean.mixedSpace K)) := by
    have h := summable_sum (s := (Finset.univ : Finset (𝓞 K ⧸ 𝔣))) fun a _ => hph a
    exact h.congr fun m => by rw [Finset.sum_mul]
  have h2 := (Equiv.summable_iff (rayDualTransportEquiv K 𝔣 𝔞 h𝔣 hc ht')).mpr hsum
  refine h2.congr fun z => ?_
  rw [Function.comp_apply]
  rw [rayDualTransportEquiv_apply K 𝔣 𝔞 h𝔣 hc ht' z]
  congr 1
  rw [← phaseSum_eq_gaussCore χ h𝔣 S x₀ (z : K)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  rw [inner_placeScale, LinearEquiv.apply_symm_apply]

private def rayInvConst (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) : ℂ :=
  uWeight K 𝔣 χ S 𝔞 x₀
    * ((-Complex.I) ^ S.card * (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card)
    * (ZLattice.covolume (dilRayLattice K 𝔣 𝔞 h𝔣) volume : ℂ)⁻¹
    * gaussFT (rayScale K 𝔣 𝔞) (0 : euclidean.mixedSpace K)

private def rayInvPolarCoeff (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) : ℂ :=
  rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀ * polyS (realUnit K) S (0 : euclidean.mixedSpace K)

private def rayInvDual (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (s : ℂ) (t : realSpace K) : ℂ :=
  rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀ * rayMellinWeight K S (1 - s) t
    * ∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
        gaussCore χ h𝔣 S (x₀ * (z.1 : K))
          * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
          * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
              * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ)

private theorem rayFoldMellinIntegrand_inv_gen [Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
    (hS : IsParity K 𝔣 χ S)
    {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀)
    {t : realSpace K} (ht : t ∈ orthant K) (s : ℂ) :
    rayFoldMellinIntegrand K 𝔣 χ S 𝔞 (rayScale K 𝔣 𝔞) s t⁻¹
      = rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ s t
        + ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)) * rayInvPolarCoeff K 𝔣 χ S 𝔞 h𝔣 x₀)
            * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2) := by
  have htw : ∀ w, 0 < t w := ht
  have hti : ∀ w, 0 < t⁻¹ w := fun w => by
    rw [Pi.inv_apply]
    exact inv_pos.mpr (htw w)
  have hc : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  haveI : DiscreteTopology (dilRayLattice K 𝔣 𝔞 h𝔣) :=
    inferInstanceAs (DiscreteTopology (dilLattice K (rayModIdeal K 𝔣 𝔞 h𝔣)))
  haveI : IsZLattice ℝ (dilRayLattice K 𝔣 𝔞 h𝔣) :=
    inferInstanceAs (IsZLattice ℝ (dilLattice K (rayModIdeal K 𝔣 𝔞 h𝔣)))

  rw [rayFoldMellinIntegrand,
    tsum_rayFoldSummand_eq_coset K 𝔣 χ S 𝔞 h𝔣 h𝔣' hS hx₀ (rayScale K 𝔣 𝔞) t⁻¹
      (rayFoldSummand_summable K 𝔣 χ S 𝔞 h𝔣 h𝔣' hc hti)]

  have h2a : ∀ a : 𝓞 K ⧸ 𝔣,
      (∑' v : dilRayLattice K 𝔣 𝔞 h𝔣,
          polyS (realUnit K) S ((v : euclidean.mixedSpace K) + bridgeRep K 𝔣 x₀ a)
            * ((Real.exp (-π * rayScale K 𝔣 𝔞 * rayDilForm K t⁻¹
                ((v : euclidean.mixedSpace K) + bridgeRep K 𝔣 x₀ a)) : ℝ) : ℂ))
        = ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
            * ∑' v' : scaleLattice K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
                  (rayFlatScaleVec_pos K hc hti) (dilRayLattice K 𝔣 𝔞 h𝔣),
                oddGaussian (realUnit K) 1 S ((v' : euclidean.mixedSpace K)
                  + placeScale K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
                      (rayFlatScaleVec_pos K hc hti) (bridgeRep K 𝔣 x₀ a)) :=
    fun a => tsum_dil_eq_scaled_oddGaussian K 𝔣 S 𝔞 h𝔣 hc hti (bridgeRep K 𝔣 x₀ a)
  simp only [h2a]
  rw [show (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)
        * (((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
          * ∑' v' : scaleLattice K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
                (rayFlatScaleVec_pos K hc hti) (dilRayLattice K 𝔣 𝔞 h𝔣),
              oddGaussian (realUnit K) 1 S ((v' : euclidean.mixedSpace K)
                + placeScale K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
                    (rayFlatScaleVec_pos K hc hti) (bridgeRep K 𝔣 x₀ a))))
      = ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
          * ∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)
            * ∑' v' : scaleLattice K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
                  (rayFlatScaleVec_pos K hc hti) (dilRayLattice K 𝔣 𝔞 h𝔣),
                oddGaussian (realUnit K) 1 S ((v' : euclidean.mixedSpace K)
                  + placeScale K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
                      (rayFlatScaleVec_pos K hc hti) (bridgeRep K 𝔣 x₀ a)) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring]

  rw [scaled_coset_poisson_dual K 𝔣 χ S 𝔞 h𝔣 hc hti x₀]

  have heval : ∀ z : ↥((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      : FractionalIdeal (𝓞 K)⁰ K),
      gaussCore χ h𝔣 S (x₀ * (z : K))
        * (polyS (realUnit K) S ((placeScale K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
              (rayFlatScaleVec_pos K hc hti)).symm (dualPt K (z : K)))
          * gaussFT 1 ((placeScale K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
              (rayFlatScaleVec_pos K hc hti)).symm (dualPt K (z : K))))
      = ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
          * (gaussCore χ h𝔣 S (x₀ * (z : K))
            * (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ)) := fun z => by
    rw [polyS_realUnit_placeScale_symm, polyS_realUnit_dualPt,
      gaussFT_one_placeScale_symm_flat K hc hti (dualPt K (z : K)), inv_inv,
      rayDilForm_dualPt]
    ring
  simp only [heval]
  rw [tsum_mul_left]

  have hCF0 : ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (inv_ne_zero ?_)
    exact (Finset.prod_pos fun v _ => rayFlatScaleVec_pos K hc hti v.1).ne'
  have hsumF : Summable fun z : ↥((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      : FractionalIdeal (𝓞 K)⁰ K) =>
      gaussCore χ h𝔣 S (x₀ * (z : K))
        * (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
        * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
            * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ) := by
    have h1 := (summable_ray_dual_series K 𝔣 χ S 𝔞 h𝔣 hc hti x₀).congr heval
    have h2 := h1.mul_left (((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹
        : ℝ)) : ℂ))⁻¹
    refine h2.congr fun z => ?_
    rw [← mul_assoc, inv_mul_cancel₀ hCF0, one_mul]
  rw [hsumF.tsum_eq_add_tsum_ite ⟨0, FractionalIdeal.zero_mem _⟩]

  rw [show gaussCore χ h𝔣 S (x₀ * (((⟨0, FractionalIdeal.zero_mem _⟩
        : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K))) : K))
      * (∏ v ∈ S, ((embedding_of_isReal v.2 (((⟨0, FractionalIdeal.zero_mem _⟩
          : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K))) : K) : ℝ) : ℂ))
      * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
          * torusForm K t (mixedEmbedding K (((⟨0, FractionalIdeal.zero_mem _⟩
              : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K))) : K))) : ℝ) : ℂ)
      = (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)) * polyS (realUnit K) S 0 by
    rw [show (((⟨0, FractionalIdeal.zero_mem _⟩
          : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K))) : K) = (0 : K) from rfl,
      mul_zero, gaussCore_zero,
      show (∏ v ∈ S, ((embedding_of_isReal v.2 (0 : K) : ℝ) : ℂ)) = polyS (realUnit K) S 0 by
        rw [polyS_realUnit]
        refine Finset.prod_congr rfl fun v _ => ?_
        simp [map_zero],
      map_zero, show torusForm K t (0 : mixedSpace K) = 0 by simp [torusForm],
      mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one]]

  rw [show (∑' z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K),
      if z = (⟨0, FractionalIdeal.zero_mem _⟩
          : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K)) then (0 : ℂ) else
        gaussCore χ h𝔣 S (x₀ * (z : K))
          * (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
          * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
              * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ))
      = ∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          gaussCore χ h𝔣 S (x₀ * (z.1 : K))
            * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ) by
    refine ((tsum_subtype_eq_of_support_subset
        (f := fun z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
          if z = (⟨0, FractionalIdeal.zero_mem _⟩
              : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K)) then (0 : ℂ) else
            gaussCore χ h𝔣 S (x₀ * (z : K))
              * (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
              * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                  * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ))
        (s := {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) | (z : K) ≠ 0})
        ?_).symm).trans (tsum_congr fun z => ?_)
    · intro z hz
      by_contra h0
      simp only [Set.mem_setOf_eq, not_not] at h0
      exact hz (if_pos (Subtype.ext h0))
    · have hz2 : (z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K))
          ≠ ⟨0, FractionalIdeal.zero_mem _⟩ := fun h0 => z.2 (by simp [h0])
      exact if_neg hz2]

  rw [rayInvDual, rayInvPolarCoeff, rayInvConst, rayMellinWeight, rayMellinWeight,
    gaussFT_zero_eq_inv_sqrt_pow K hc]

  rw [show ZLattice.covolume (scaleLattice K (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹)
        (rayFlatScaleVec_pos K hc hti) (dilRayLattice K 𝔣 𝔞 h𝔣)) volume
      = Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K * torusNorm K t⁻¹)
          * ZLattice.covolume (dilRayLattice K 𝔣 𝔞 h𝔣) volume by
    rw [covolume_scaleLattice, prod_rayFlatScaleVec_pow_mult K hc hti]]

  rw [Complex.ofReal_mul, mul_inv]
  rw [show Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K * torusNorm K t⁻¹)
      = Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K) * (Real.sqrt (torusNorm K t))⁻¹ by
    rw [Real.sqrt_mul (pow_nonneg hc.le _), torusNorm_inv, Real.sqrt_inv],
    Complex.ofReal_mul, mul_inv,
    show ((((Real.sqrt (torusNorm K t))⁻¹ : ℝ)) : ℂ)
        = (((Real.sqrt (torusNorm K t) : ℝ) : ℂ))⁻¹ from Complex.ofReal_inv _,
    inv_inv,
    show ((((Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K))⁻¹ : ℝ)) : ℂ)
        = (((Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K) : ℝ) : ℂ))⁻¹ from
      Complex.ofReal_inv _]
  have htN : 0 < torusNorm K t := torusNorm_pos K htw
  have htN0 : ((torusNorm K t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htN.ne'
  have harg : ((torusNorm K t : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg htN.le]
    exact Real.pi_ne_zero.symm
  rw [show ((torusNorm K t⁻¹ : ℝ) : ℂ) = (((torusNorm K t : ℝ) : ℂ))⁻¹ by
      rw [torusNorm_inv, Complex.ofReal_inv],
    Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  rw [show ((Real.sqrt (torusNorm K t) : ℝ) : ℂ)
      = ((torusNorm K t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ) by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow htN.le]]
  rw [show ((1 : ℂ) - s) / 2 = (((1 / 2 : ℝ) : ℝ) : ℂ) + -(s / 2) by push_cast; ring,
    Complex.cpow_add _ _ htN0]
  have hSW : raySWeight K S t⁻¹ = (raySWeight K S t)⁻¹ := by
    rw [raySWeight, raySWeight, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Pi.inv_apply, Real.sqrt_inv, Complex.ofReal_inv]
  rw [hSW]

  have hplace : ∀ v : {w : InfinitePlace K // IsReal w},
      (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹
        * (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹
      = (rayScale K 𝔣 𝔞)⁻¹ * (Real.sqrt (t v.1) * Real.sqrt (t v.1)) := fun v => by
    have h2 := rayFlatScaleVec_sq K hc hti v.1
    rw [Pi.inv_apply] at h2
    rw [← mul_inv, ← pow_two, h2, mul_inv, inv_inv, Real.mul_self_sqrt (htw v.1).le]
  have hreal : (∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹
      * (∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹
      = ((rayScale K 𝔣 𝔞)⁻¹) ^ S.card
          * ∏ v ∈ S, Real.sqrt (t v.1) * Real.sqrt (t v.1) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      show (∏ v ∈ S, (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹
          * (rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹)
        = ∏ v ∈ S, (rayScale K 𝔣 𝔞)⁻¹ * (Real.sqrt (t v.1) * Real.sqrt (t v.1)) from
        Finset.prod_congr rfl fun v _ => hplace v,
      Finset.prod_mul_distrib, Finset.prod_const]
  have hCF2 : ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
      * ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K 𝔣 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
      = (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card
          * (raySWeight K S t * raySWeight K S t) := by
    rw [← Complex.ofReal_mul, hreal, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_inv, raySWeight, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
    rw [show (∏ v ∈ S, ((Real.sqrt (t v.1) * Real.sqrt (t v.1) : ℝ) : ℂ))
        = ∏ v ∈ S, (((Real.sqrt (t (v : InfinitePlace K)) : ℝ) : ℂ)
            * ((Real.sqrt (t (v : InfinitePlace K)) : ℝ) : ℂ)) from
      Finset.prod_congr rfl fun v _ => by push_cast; ring]
    rw [one_div]

  rcases Finset.eq_empty_or_nonempty S with hSe | hSne
  · simp only [hSe, Finset.prod_empty, Finset.card_empty, pow_zero, raySWeight,
      Complex.ofReal_one, inv_one, one_mul, mul_one]
    ring
  · have hp00 : polyS (realUnit K) S 0 = 0 := by
      obtain ⟨v, hv⟩ := hSne
      rw [polyS_realUnit]
      exact Finset.prod_eq_zero hv (by simp)
    simp only [hp00, mul_zero, zero_mul, zero_add, add_zero]
    have hSW0 : raySWeight K S t ≠ 0 := by
      rw [raySWeight]
      exact Finset.prod_ne_zero_iff.mpr fun v _ =>
        Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (htw v.1))
    have hSWc : (raySWeight K S t)⁻¹ * raySWeight K S t = 1 := inv_mul_cancel₀ hSW0
    linear_combination (uWeight K 𝔣 χ S 𝔞 x₀ * (-Complex.I) ^ S.card
        * ((((ZLattice.covolume (dilRayLattice K 𝔣 𝔞 h𝔣) volume : ℝ)) : ℂ))⁻¹
        * ((((Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K) : ℝ)) : ℂ))⁻¹
        * (((torusNorm K t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ)
            * ((torusNorm K t : ℝ) : ℂ) ^ (-(s / 2)))
        * (raySWeight K S t)⁻¹
        * ∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
            gaussCore χ h𝔣 S (x₀ * (z.1 : K))
              * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
              * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                  * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ)) * hCF2
      + (uWeight K 𝔣 χ S 𝔞 x₀ * (-Complex.I) ^ S.card
        * ((((ZLattice.covolume (dilRayLattice K 𝔣 𝔞 h𝔣) volume : ℝ)) : ℂ))⁻¹
        * ((((Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K) : ℝ)) : ℂ))⁻¹
        * (((torusNorm K t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ)
            * ((torusNorm K t : ℝ) : ℂ) ^ (-(s / 2)))
        * (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card * raySWeight K S t
        * ∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
            gaussCore χ h𝔣 S (x₀ * (z.1 : K))
              * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
              * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                  * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ)) * hSWc

private theorem rayFoldMellinIntegrand_inv [Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
    (hS : IsParity K 𝔣 χ S) (hprim : IsPrimitiveMod K 𝔣 χ)
    {y : K} (hy : IsGaussDatum K 𝔣 χ y)
    {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀)
    {t : realSpace K} (ht : t ∈ orthant K) (s : ℂ) :
    rayFoldMellinIntegrand K 𝔣 χ S 𝔞 (rayScale K 𝔣 𝔞) s t⁻¹
      = (-Complex.I) ^ S.card
            * (gaussSumAt K 𝔣 χ h𝔣 S y / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))
            * (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card
            * rayFoldMellinIntegrand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
                (rayDualIdeal K 𝔣 h𝔣 𝔞) (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) (1 - s) t
        + ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)) * rayInvPolarCoeff K 𝔣 χ S 𝔞 h𝔣 x₀)
            * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2) := by
  obtain ⟨h0, hc0⟩ := hx₀.spanFI_coprime
  have hx₀𝔞 : x₀ ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := hx₀.1
  have hc : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  rw [rayFoldMellinIntegrand_inv_gen K 𝔣 χ S 𝔞 h𝔣 h𝔣' hS hx₀ ht s]
  congr 1

  rw [rayInvDual, rayFoldMellinIntegrand]

  have hc' : rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞) = (rayScale K 𝔣 𝔞)⁻¹ := by
    have h := rayScale_mul_rayScale_dual (K := K) h𝔣 𝔞
    field_simp
    linear_combination h

  have hterm : ∀ z : ((rayDualIdeal K 𝔣 h𝔣 𝔞
      : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K),
      rayFoldSummand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 𝔞)
          (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) t (z : K)
        = ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K)
              * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S (z : K))
            * (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ) := fun z => by
    rw [rayFoldSummand,
      show uWeight K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 𝔞) (z : K)
        = (starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K)
            * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S (z : K) by
        rw [uWeight, ← coe_rayDualIdeal_inv h𝔣 𝔞]
        exact congrArg (· * signAt K S (z : K)) (chiIdeal_conjChar 𝔣 χ _),
      hc', one_div]

  have hdz : rayFoldSummand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 𝔞)
      (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) t
      (((⟨0, FractionalIdeal.zero_mem _⟩ : ((rayDualIdeal K 𝔣 h𝔣 𝔞
          : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) : K)) = 0 := by
    rw [show (((⟨0, FractionalIdeal.zero_mem _⟩ : ((rayDualIdeal K 𝔣 h𝔣 𝔞
          : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) : K)) = (0 : K) from rfl,
      rayFoldSummand, uWeight]
    simp [FractionalIdeal.spanSingleton_zero, chiIdeal_zero]
  rw [show (∑' x : ((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
        : FractionalIdeal (𝓞 K)⁰ K),
      rayFoldSummand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 𝔞)
        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) t (x : K))
      = ∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          rayFoldSummand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 𝔞)
            (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) t (z.1 : K) by
    refine ((tsum_subtype_eq_of_support_subset
        (f := fun z : ((rayDualIdeal K 𝔣 h𝔣 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
            : FractionalIdeal (𝓞 K)⁰ K) =>
          rayFoldSummand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 𝔞)
            (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) t (z : K))
        (s := {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) | (z : K) ≠ 0})
        ?_)).symm
    intro z hz
    by_contra h0
    simp only [Set.mem_setOf_eq, not_not] at h0
    refine hz ?_
    have hz0 : z = ⟨0, FractionalIdeal.zero_mem _⟩ := Subtype.ext h0
    rw [hz0]
    exact hdz]

  have hseam : ∀ z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
      gaussCore χ h𝔣 S (x₀ * (z.1 : K))
        = gaussSumAt K 𝔣 χ h𝔣 S y
          * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)))
            * signAt K S x₀)
          * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (z.1 : K)
              * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S (z.1 : K)) :=
    fun z => by
      refine gaussCore_mul_eq_gaussSum_mul χ h𝔣 h𝔣' S hS hprim hy 𝔞 hx₀𝔞 h0 hc0 ?_
      rw [← coe_rayDualIdeal h𝔣 𝔞]
      exact z.1.2
  simp only [hterm, hseam]

  rw [show (∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
      gaussSumAt K 𝔣 χ h𝔣 S y
          * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)))
            * signAt K S x₀)
          * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (z.1 : K)
              * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S (z.1 : K))
        * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
        * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
            * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
      = (gaussSumAt K 𝔣 χ h𝔣 S y
          * ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
              * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)))
            * signAt K S x₀))
        * ∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
            ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (z.1 : K)
                * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S (z.1 : K))
              * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
              * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                  * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ) by
    rw [← tsum_mul_left]
    exact tsum_congr fun z => by ring]

  rw [rayInvConst, gaussFT_zero_eq_inv_sqrt_pow K hc,
    show ((((Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K))⁻¹ : ℝ)) : ℂ)
        = (((1 / rayScale K 𝔣 𝔞) ^ ((Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) by
      congr 1
      rw [one_div, Real.inv_rpow hc.le]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (rayScale K 𝔣 𝔞) (Module.finrank ℚ K),
        ← Real.rpow_mul hc.le]
      congr 1
      ring,
    show ZLattice.covolume (dilRayLattice K 𝔣 𝔞 h𝔣) volume
        = (FractionalIdeal.absNorm ((rayModIdeal K 𝔣 𝔞 h𝔣 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
            : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * Real.sqrt |(discr K : ℝ)| from
      covolume_mixedDilLattice_idealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣),
    absNorm_rayModIdeal (K := K) h𝔣 𝔞]
  have hK := congrArg (fun r : ℝ => (r : ℂ)) (rayFE_constants (K := K) 𝔣 h𝔣 𝔞 0 one_pos)
  simp only [pow_zero, one_mul, mul_one, Real.one_rpow] at hK
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv] at hK
  have hu := uWeight_mul_conj 𝔣 χ S 𝔞 h0 hc0 h𝔣
  linear_combination ((-Complex.I) ^ S.card * (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card
      * rayMellinWeight K S (1 - s) t * gaussSumAt K 𝔣 χ h𝔣 S y
      * (∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (z.1 : K)
              * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S (z.1 : K))
            * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
      * ((((Ideal.absNorm 𝔣 : ℝ) * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
          * Real.sqrt |(discr K : ℝ)| : ℝ)) : ℂ)⁻¹
      * (((1 / rayScale K 𝔣 𝔞) ^ ((Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ)) * hu
    + ((-Complex.I) ^ S.card * (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card
      * rayMellinWeight K S (1 - s) t * gaussSumAt K 𝔣 χ h𝔣 S y
      * (∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          ((starRingEnd ℂ) (chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (z.1 : K)
              * ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 * diffFI K))) * signAt K S (z.1 : K))
            * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))) * hK

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_RayFoldInvBody
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_RayFoldInvPolar

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
p2m_open "MeasureTheory Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
open scoped nonZeroDivisors Classical Real FourierTransform InnerProductSpace

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem rayInvPolarCoeff_eq_zero_of_ne_empty (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (hS : S ≠ ∅) :
    rayInvPolarCoeff K 𝔣 χ S 𝔞 h𝔣 x₀ = 0 := by
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  rw [rayInvPolarCoeff, polyS_realUnit]
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero hv (by simp))

private theorem rayInvPolarCoeff_eq (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (hS : S = ∅) :
    rayInvPolarCoeff K 𝔣 χ S 𝔞 h𝔣 x₀
      = uWeight K 𝔣 χ S 𝔞 x₀ * ((Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))⁻¹ := by
  subst hS
  have hc : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  rw [rayInvPolarCoeff, rayInvConst, polyS_realUnit]
  simp only [Finset.prod_empty, Finset.card_empty, pow_zero, mul_one]
  rw [gaussFT_zero_eq_inv_sqrt_pow K hc,
    show ((((Real.sqrt (rayScale K 𝔣 𝔞 ^ Module.finrank ℚ K))⁻¹ : ℝ)) : ℂ)
        = (((1 / rayScale K 𝔣 𝔞) ^ ((Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) by
      congr 1
      rw [one_div, Real.inv_rpow hc.le]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (rayScale K 𝔣 𝔞) (Module.finrank ℚ K),
        ← Real.rpow_mul hc.le]
      congr 1
      ring,
    show ZLattice.covolume (dilRayLattice K 𝔣 𝔞 h𝔣) volume
        = (FractionalIdeal.absNorm ((rayModIdeal K 𝔣 𝔞 h𝔣 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
            : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * Real.sqrt |(discr K : ℝ)| from
      covolume_mixedDilLattice_idealLattice K (rayModIdeal K 𝔣 𝔞 h𝔣),
    absNorm_rayModIdeal (K := K) h𝔣 𝔞]
  have hK := congrArg (fun r : ℝ => (r : ℂ)) (rayFE_constants (K := K) 𝔣 h𝔣 𝔞 0 one_pos)
  simp only [pow_zero, one_mul, mul_one, Real.one_rpow] at hK
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv] at hK
  linear_combination uWeight K 𝔣 χ ∅ 𝔞 x₀ * hK

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_RayFoldInvPolar
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_M4aTorus_RayTc2

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
p2m_open "M4aTorus"

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
p2m_open "MeasureTheory Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
open scoped nonZeroDivisors Classical Real

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})

private def tc2Const : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ)

private def tc2Alpha (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  fun _ => tc2Const K * ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ) ^ S.card

private theorem differentiable_tc2Alpha (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (tc2Alpha K 𝔣 S 𝔞) :=
  differentiable_const _

private theorem tc2Alpha_rayDualIdeal (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    tc2Alpha K 𝔣 S (rayDualIdeal K 𝔣 h𝔣 𝔞) s
      = tc2Alpha K 𝔣 S 𝔞 (1 - s) * (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card := by
  unfold tc2Alpha
  have hc : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  have hcd : rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞) = (rayScale K 𝔣 𝔞)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (rayScale_mul_rayScale_dual (K := K) h𝔣 𝔞)).symm
  have hne : ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne'
  have hne' : ((rayScale K 𝔣 𝔞 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  rw [hcd, Real.sqrt_inv, ofReal_inv, inv_pow, one_div, inv_pow, mul_assoc]
  congr 1
  field_simp
  rw [← pow_mul, mul_comm S.card 2, pow_mul, pow_two, ← ofReal_mul, Real.mul_self_sqrt hc.le]

private theorem classGroup_mk_rayDualIdeal (h𝔣 : 𝔣 ≠ ⊥) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (rayDualIdeal K 𝔣 h𝔣 𝔞)
      = codifferentClass K
          * (ClassGroup.mk K (Units.mk0 ((𝔣 : FractionalIdeal (𝓞 K)⁰ K))
              (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣)))⁻¹
          * (ClassGroup.mk K 𝔞)⁻¹ :=
  calc ClassGroup.mk K (rayDualIdeal K 𝔣 h𝔣 𝔞)
      = codifferentClass K * (ClassGroup.mk K (Units.mk0 _
          (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣) * 𝔞))⁻¹ := idealClass_dualIdealUnit K _
    _ = _ := by rw [map_mul, mul_inv, mul_assoc]

private theorem bijective_classGroup_mk_rayDualIdeal_comp {ι : Type*} (h𝔣 : 𝔣 ≠ ⊥)
    (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞 i)) :
    Function.Bijective fun i => ClassGroup.mk K (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) := by
  set a : ClassGroup (𝓞 K) := codifferentClass K * (ClassGroup.mk K (Units.mk0
    ((𝔣 : FractionalIdeal (𝓞 K)⁰ K)) (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔣)))⁻¹
  have hfun : (fun i => ClassGroup.mk K (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)))
      = (fun C => a * C⁻¹) ∘ (fun i => ClassGroup.mk K (𝔞 i)) :=
    funext fun i => classGroup_mk_rayDualIdeal K 𝔣 h𝔣 (𝔞 i)
  rw [hfun]
  exact Function.Bijective.comp
    (⟨fun C => a * C⁻¹, fun C => (a⁻¹ * C)⁻¹, fun C => by group, fun C => by group⟩ :
      ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K)).bijective hbij

section RayTc1

variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private def rayOrbitKernel (c : ℝ) (x : K) (s : ℂ) (t : realSpace K) : ℂ :=
  rayFoldSummand K 𝔣 χ S 𝔞 c t x * rayMellinWeight K S s t

private theorem rayOrbitKernel_unit_mul (c : ℝ) (s : ℂ) (u : (𝓞 K)ˣ) (t : realSpace K) (x : K) :
    rayOrbitKernel K 𝔣 χ S 𝔞 c (((u : 𝓞 K) : K) * x) s t
      = rayOrbitKernel K 𝔣 χ S 𝔞 c x s (unitTorus K u t) := by
  unfold rayOrbitKernel
  rw [rayFoldSummand_unit_mul K 𝔣 χ S 𝔞 c u t x, rayMellinWeight_unitTorus K S s u t]
  ring

private theorem rayOrbitKernel_zero (c : ℝ) (s : ℂ) (t : realSpace K) :
    rayOrbitKernel K 𝔣 χ S 𝔞 c 0 s t = 0 := by
  unfold rayOrbitKernel rayFoldSummand
  rw [uWeight, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero, zero_mul, zero_mul,
    zero_mul, zero_mul]

private def rayOrbitMellin (c : ℝ) (x : K) (s : ℂ) : ℂ :=
  ∫ t in {t : realSpace K | ∀ w, 0 < t w}, rayOrbitKernel K 𝔣 χ S 𝔞 c x s t ∂(torusHaar K)

private theorem integrableOn_rayOrbitKernel (h𝔣 : 𝔣 ≠ ⊥) (c : ℝ) (hc : 0 < c) {x : K} (hx : x ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (rayOrbitKernel K 𝔣 χ S 𝔞 c x s)
      {t : realSpace K | ∀ w, 0 < t w} (torusHaar K) := by
  have hmeas : Measurable (rayOrbitKernel K 𝔣 χ S 𝔞 c x s) :=
    (measurable_rayFoldSummand_left K 𝔣 χ S 𝔞 c x).mul (measurable_rayMellinWeight K S s)
  refine ⟨hmeas.aestronglyMeasurable.restrict, ?_⟩
  have hS := measurableSet_setOf_pos K
  refine (hasFiniteIntegral_def _ _).mpr ?_
  calc ∫⁻ t in {t | ∀ w, 0 < t w}, ‖rayOrbitKernel K 𝔣 χ S 𝔞 c x s t‖ₑ ∂(torusHaar K)
      ≤ ∫⁻ t in {t | ∀ w, 0 < t w}, ENNReal.ofReal (rayMajKernel K S c x s.re t) ∂(torusHaar K) :=
        setLIntegral_mono' hS fun t ht =>
          enorm_rayFoldSummand_mul_rayMellinWeight_le K 𝔣 χ S 𝔞 h𝔣 c s x ht
    _ < ⊤ := by
        rw [show ({t | ∀ w, 0 < t w} : Set (realSpace K)) = orthant K from rfl,
          setLIntegral_orthant_rayMajKernel_eq K S hc hx hs]
        exact ENNReal.ofReal_lt_top

private theorem aestronglyMeasurable_rayOrbitKernel (c : ℝ) (x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) (s : ℂ) :
    AEStronglyMeasurable (fun t => rayOrbitKernel K 𝔣 χ S 𝔞 c (x : K) s t)
      ((torusHaar K).restrict (foldDomain K)) :=
  ((measurable_rayFoldSummand_left K 𝔣 χ S 𝔞 c (x : K)).mul
    (measurable_rayMellinWeight K S s)).aestronglyMeasurable.restrict

private theorem summable_setIntegral_foldDomain_rayOrbitKernel (h𝔣 : 𝔣 ≠ ⊥) (c : ℝ) (hc : 0 < c)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : ({I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹} × (𝓞 K)ˣ) =>
      ∫ t in foldDomain K, rayOrbitKernel K 𝔣 χ S 𝔞 c (fracIdealGen K 𝔞 p.1) s
        (unitTorus K p.2 t) ∂(torusHaar K) := by
  have hfin := tsum_lintegral_foldDomain_enorm_rayFoldSummand_ne_top K 𝔣 χ S 𝔞 h𝔣 c hc hs

  rw [← (fracIdealNonzeroEquiv K 𝔞).symm.tsum_eq, ennreal_tsum_option] at hfin
  have hfin' : ∑' p : ({I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹} × (𝓞 K)ˣ),
      ∫⁻ t in foldDomain K, ‖rayOrbitKernel K 𝔣 χ S 𝔞 c (fracIdealGen K 𝔞 p.1) s
        (unitTorus K p.2 t)‖ₑ ∂(torusHaar K) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (le_add_self.trans_eq' ?_)
    rw [← (fracIdealOrbitEquiv K 𝔞).tsum_eq]
    refine tsum_congr fun p => ?_
    refine setLIntegral_congr_fun (measurableSet_foldDomain K) fun t _ => ?_
    rw [fracIdealNonzeroEquiv_symm_some, fracIdealOrbitEquiv_apply_val]
    exact congrArg (‖·‖ₑ) (rayOrbitKernel_unit_mul K 𝔣 χ S 𝔞 c s p.2 t (fracIdealGen K 𝔞 p.1))
  refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin') fun p => ?_
  exact (toReal_enorm _).symm.trans_le (ENNReal.toReal_mono
    (ne_top_of_le_ne_top hfin' (ENNReal.le_tsum p)) (enorm_integral_le_lintegral_enorm _))

private theorem rayFoldMellin_unfold (h𝔣 : 𝔣 ≠ ⊥) (c : ℝ) (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    rayFoldMellin K 𝔣 χ S 𝔞 c s
      = (torsionOrder K : ℂ) *
          ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹},
            rayOrbitMellin K 𝔣 χ S 𝔞 c (fracIdealGen K 𝔞 I) s := by
  have hs0 : 0 < s.re := one_pos.trans hs

  have step1 : (∫ t in foldDomain K, rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t ∂(torusHaar K))
      = ∫ t in foldDomain K, (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
          rayOrbitKernel K 𝔣 χ S 𝔞 c (x : K) s t) ∂(torusHaar K) :=
    setIntegral_congr_fun (measurableSet_foldDomain K) fun t _ => tsum_mul_right.symm

  have step2 : (∫ t in foldDomain K, (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
          rayOrbitKernel K 𝔣 χ S 𝔞 c (x : K) s t) ∂(torusHaar K))
      = ∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
          ∫ t in foldDomain K, rayOrbitKernel K 𝔣 χ S 𝔞 c (x : K) s t ∂(torusHaar K) :=
    integral_tsum (aestronglyMeasurable_rayOrbitKernel K 𝔣 χ S 𝔞 c · s)
      (tsum_lintegral_foldDomain_enorm_rayFoldSummand_ne_top K 𝔣 χ S 𝔞 h𝔣 c hc hs)

  have hsupp : Function.support (fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
        ∫ t in foldDomain K, rayOrbitKernel K 𝔣 χ S 𝔞 c (x : K) s t ∂(torusHaar K))
      ⊆ {x | (x : K) ≠ 0} := fun x hx h0 => hx (by
    simp only [show ((x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K) = 0 from h0,
      rayOrbitKernel_zero, integral_zero])
  have step3 : (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
        ∫ t in foldDomain K, rayOrbitKernel K 𝔣 χ S 𝔞 c (x : K) s t ∂(torusHaar K))
      = ∑' p : ({I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹} × (𝓞 K)ˣ),
          ∫ t in foldDomain K, rayOrbitKernel K 𝔣 χ S 𝔞 c (fracIdealGen K 𝔞 p.1) s
            (unitTorus K p.2 t) ∂(torusHaar K) := by
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    show (∑' x : {x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (x : K) ≠ 0},
        ∫ t in foldDomain K, rayOrbitKernel K 𝔣 χ S 𝔞 c (x.1 : K) s t ∂(torusHaar K)) = _
    rw [← (fracIdealOrbitEquiv K 𝔞).tsum_eq]
    refine tsum_congr fun p => ?_
    refine setIntegral_congr_fun (measurableSet_foldDomain K) fun t _ => ?_
    rw [show (((fracIdealOrbitEquiv K 𝔞 p).1 :
        (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K) = ((p.2 : 𝓞 K) : K) * fracIdealGen K 𝔞 p.1 from
      fracIdealOrbitEquiv_apply_val K 𝔞 p.1 p.2, rayOrbitKernel_unit_mul]

  rw [rayFoldMellin, step1, step2, step3,
    (summable_setIntegral_foldDomain_rayOrbitKernel K 𝔣 χ S 𝔞 h𝔣 c hc hs).tsum_prod,
    ← tsum_mul_left]
  refine tsum_congr fun I => ?_
  rw [tsum_units_setIntegral_foldDomain_complex K
    (integrableOn_rayOrbitKernel K 𝔣 χ S 𝔞 h𝔣 c hc (fracIdealGen_ne_zero K 𝔞 I) hs0)]
  rfl

private def rayGammaBlock (c : ℝ) (s : ℂ) : ℂ :=
  ((Real.sqrt c : ℝ) : ℂ)⁻¹ ^ S.card * ((2 : ℂ)⁻¹) ^ nrComplexPlaces K
    * (((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ (nrRealPlaces K - S.card) * Gammaℝ (s + 1) ^ S.card *
        Gammaℂ s ^ nrComplexPlaces K)

private def rayPlaceExp (s : ℂ) (w : InfinitePlace K) : ℂ :=
  (mult w : ℂ) * (s / 2) + if h : IsReal w then (if ⟨w, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0

private def rayPlaceRate (c : ℝ) (x : K) (w : InfinitePlace K) : ℝ :=
  Real.pi * c * (mult w : ℝ) * (w x) ^ 2

omit [NumberField K] in
private theorem rayPlaceRate_pos {c : ℝ} (hc : 0 < c) {x : K} (hx : x ≠ 0) (w : InfinitePlace K) :
    0 < rayPlaceRate K c x w := by
  unfold rayPlaceRate
  have h2 : (0 : ℝ) < mult w := by exact_mod_cast (mult_pos (w := w))
  have h3 : 0 < w x := pos_iff.mpr hx
  positivity

private def rayPlaceIntegrand (c : ℝ) (x : K) (s : ℂ) (w : InfinitePlace K) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (rayPlaceExp K S s w - 1) * Complex.exp (-((rayPlaceRate K c x w : ℂ) * (r : ℂ)))

private theorem ray_pow_cpow_eq_cpow_mul {r : ℝ} (hr : 0 ≤ r) (m : ℕ) (z : ℂ) :
    ((r ^ m : ℝ) : ℂ) ^ z = (r : ℂ) ^ ((m : ℂ) * z) := by
  rw [show (r ^ m : ℝ) = r ^ ((m : ℕ) : ℝ) by rw [Real.rpow_natCast],
    ← Complex.cpow_mul_ofReal_nonneg hr]
  push_cast
  rfl

private theorem ray_ofReal_prod_cpow {ι : Type*} (T : Finset ι) (f : ι → ℝ) (z : ℂ)
    (hf : ∀ i ∈ T, 0 ≤ f i) : ((∏ i ∈ T, f i : ℝ) : ℂ) ^ z = ∏ i ∈ T, ((f i : ℝ) : ℂ) ^ z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.prod_insert haT, Finset.prod_insert haT, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a (Finset.mem_insert_self a T))
        (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private theorem ray_prod_cpow_eq_cpow_sum {ι : Type*} (T : Finset ι) {b : ℂ} (hb : b ≠ 0) (z : ι → ℂ) :
    ∏ i ∈ T, b ^ z i = b ^ (∑ i ∈ T, z i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.prod_insert haT, Finset.sum_insert haT, Complex.cpow_add _ _ hb, ih]

private theorem ray_prodS_cpow_eq_prod_indicator (z : ℂ) (t : realSpace K) :
    ∏ v ∈ S, ((t v : ℝ) : ℂ) ^ z
      = ∏ w : InfinitePlace K, ((t w : ℝ) : ℂ)
          ^ (if h : IsReal w then (if ⟨w, h⟩ ∈ S then z else 0) else 0) := by
  classical
  rw [prod_eq_prod_mul_prod,
    show (∏ v : {w : InfinitePlace K // IsComplex w}, ((t v.1 : ℝ) : ℂ)
          ^ (if h : IsReal v.1 then (if ⟨v.1, h⟩ ∈ S then z else 0) else 0)) = 1 from
      Finset.prod_eq_one fun v _ => by
        rw [dif_neg (not_isReal_iff_isComplex.mpr v.2), Complex.cpow_zero],
    mul_one,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset {w : InfinitePlace K // IsReal w})
      (· ∈ S),
    Finset.filter_mem_eq_inter, Finset.univ_inter,
    show (∏ v ∈ Finset.filter (¬ · ∈ S)
          (Finset.univ : Finset {w : InfinitePlace K // IsReal w}),
        ((t v.1 : ℝ) : ℂ) ^ (if h : IsReal v.1 then (if ⟨v.1, h⟩ ∈ S then z else 0) else 0)) = 1 from
      Finset.prod_eq_one fun v hv => by
        rw [dif_pos v.2, if_neg (Finset.mem_filter.mp hv).2, Complex.cpow_zero],
    mul_one]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvS : (⟨v.1, v.2⟩ : {w : InfinitePlace K // IsReal w}) ∈ S := by simpa using hv
  rw [dif_pos v.2, if_pos hvS]

private theorem density_mul_rayGaussian_eq_prod (c : ℝ) {x : K} (s : ℂ) {t : realSpace K}
    (ht : ∀ w, 0 < t w) :
    (∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹).toReal •
        (((Real.exp (-π * c * torusForm K t (mixedEmbedding K x)) : ℝ) : ℂ)
          * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) * raySWeight K S t)
      = ∏ w : InfinitePlace K, rayPlaceIntegrand K S c x s w (t w) := by
  have hexp : Real.exp (-π * c * torusForm K t (mixedEmbedding K x))
      = ∏ w : InfinitePlace K, Real.exp (-(rayPlaceRate K c x w * t w)) := by
    rw [torusForm, ← Real.exp_sum, Finset.mul_sum]
    exact congrArg Real.exp (Finset.sum_congr rfl fun w _ => by
      rw [normAtPlace_apply, rayPlaceRate]; ring)
  have hN : ((torusNorm K t : ℝ) : ℂ) ^ (s / 2)
      = ∏ w : InfinitePlace K, ((t w : ℝ) : ℂ) ^ ((mult w : ℂ) * (s / 2)) := by
    rw [torusNorm, ray_ofReal_prod_cpow _ _ _ fun w _ => pow_nonneg (ht w).le _]
    exact Finset.prod_congr rfl fun w _ => ray_pow_cpow_eq_cpow_mul (ht w).le (mult w) (s / 2)
  have hSW : raySWeight K S t = ∏ v ∈ S, ((t v : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    unfold raySWeight
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (ht v).le]
    push_cast; rfl

  rw [ENNReal.toReal_prod, hexp, hN, Complex.real_smul, Complex.ofReal_prod, Complex.ofReal_prod,
    show ∀ a b c d : ℂ, a * (b * c * d) = a * (b * c) * d from fun _ _ _ _ => by ring,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, hSW,
    ray_prodS_cpow_eq_prod_indicator K S ((1 : ℂ) / 2) t, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (ht w).le), rayPlaceIntegrand, rayPlaceExp,
    show (mult w : ℂ) * (s / 2)
        + (if h : IsReal w then (if ⟨w, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0) - 1
      = (mult w : ℂ) * (s / 2)
        + ((if h : IsReal w then (if ⟨w, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0) - 1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ht w).ne'),
    Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (ht w).ne'), Complex.cpow_one,
    Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_exp]
  ring

private theorem uWeight_fracIdealGen_eq
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) :
    uWeight K 𝔣 χ S 𝔞 (fracIdealGen K 𝔞 I)
      = chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1) * signAt K S (fracIdealGen K 𝔞 I) := by
  rw [uWeight, spanSingleton_fracIdealGen, Units.val_mul,
    mul_comm ((𝔞 : FractionalIdeal (𝓞 K)⁰ K)), mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one]

omit [NumberField K] in

private theorem signAt_mul_prod_embedding_eq (x : K) :
    signAt K S x * (∏ v ∈ S, ((embedding_of_isReal v.2 x : ℝ) : ℂ))
      = ∏ v ∈ S, (((v : InfinitePlace K) x : ℝ) : ℂ) := by
  have hcast : ∀ s : SignType, ((s : ℤ) : ℂ) = ((s : ℝ) : ℂ) := fun s => by
    rcases s with _ | _ | _ <;> simp
  rw [signAt, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← norm_embedding_of_isReal v.2, Real.norm_eq_abs,
    ← sign_mul_self (embedding_of_isReal v.2 x), ofReal_mul, hcast]

private theorem rayOrbitKernel_fracIdealGen_factored
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) (c : ℝ) (s : ℂ)
    (t : realSpace K) :
    rayOrbitKernel K 𝔣 χ S 𝔞 c (fracIdealGen K 𝔞 I) s t
      = (chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
          * ∏ v ∈ S, (((v : InfinitePlace K) (fracIdealGen K 𝔞 I) : ℝ) : ℂ))
        * (((Real.exp (-π * c * torusForm K t (mixedEmbedding K (fracIdealGen K 𝔞 I))) : ℝ) : ℂ)
            * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) * raySWeight K S t) := by
  rw [rayOrbitKernel, rayFoldSummand, uWeight_fracIdealGen_eq K 𝔣 χ S 𝔞 I, rayMellinWeight,
    mul_assoc (chiIdeal K 𝔣 χ _) (signAt K S _), signAt_mul_prod_embedding_eq]
  ring

private theorem setIntegral_orthant_rayGaussian_eq_prod (c : ℝ) (hc : 0 < c) {x : K} (hx : x ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    ∫ t in {t : realSpace K | ∀ w, 0 < t w},
        (((Real.exp (-π * c * torusForm K t (mixedEmbedding K x)) : ℝ) : ℂ)
          * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) * raySWeight K S t) ∂(torusHaar K)
      = ∏ w : InfinitePlace K,
          ((rayPlaceRate K c x w : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
            * Complex.Gamma (rayPlaceExp K S s w) := by
  have hO := measurableSet_setOf_pos K
  have hfact : ∀ t : realSpace K, (∀ w, 0 < t w) →
      (∏ w : InfinitePlace K, ENNReal.ofReal (t w)⁻¹).toReal •
        (((Real.exp (-π * c * torusForm K t (mixedEmbedding K x)) : ℝ) : ℂ)
          * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) * raySWeight K S t)
      = ∏ w : InfinitePlace K, rayPlaceIntegrand K S c x s w (t w) :=
    fun t ht => density_mul_rayGaussian_eq_prod K S c s ht
  have herep : ∀ w, 0 < (rayPlaceExp K S s w).re := by
    intro w
    have hm : (0 : ℝ) < mult w := by exact_mod_cast (mult_pos (w := w))
    rw [rayPlaceExp, Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.div_ofNat_re]
    split_ifs <;> simp only [Complex.div_ofNat_re, Complex.one_re, Complex.zero_re] <;> positivity
  rw [torusHaar_def,
    setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_torusDensity K)
      (Filter.Eventually.of_forall fun t => ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top)
      _ hO,
    setIntegral_congr_fun hO fun t ht => hfact t ht,
    setOf_pos_eq_pi K, MeasureTheory.volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (f := rayPlaceIntegrand K S c x s)
      (μ := fun _ => volume.restrict (Set.Ioi 0))]
  refine Finset.prod_congr rfl fun w _ => ?_
  have := Complex.integral_cpow_mul_exp_neg_mul_Ioi (herep w) (rayPlaceRate_pos K hc hx w)
  rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (rayPlaceRate_pos K hc hx w).le]
      exact Real.pi_pos.ne), ← Complex.cpow_neg] at this
  simp only [rayPlaceIntegrand]
  exact this

omit [NumberField K] in

private theorem rayGammaFactor_real_memS (s : ℂ) (w : {w : InfinitePlace K // IsReal w}) (hw : w ∈ S) :
    ((Real.pi * (mult w.1 : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w.1)
        * Complex.Gamma (rayPlaceExp K S s w.1)
      = Gammaℝ (s + 1) := by
  have hvS : (⟨w.1, w.2⟩ : {w : InfinitePlace K // IsReal w}) ∈ S := by simpa using hw
  rw [rayPlaceExp, dif_pos w.2, if_pos hvS, mult_isReal, Nat.cast_one, Nat.cast_one, mul_one,
    one_mul, show s / 2 + 1 / 2 = (s + 1) / 2 by ring, Gammaℝ_def, neg_div]

omit [NumberField K] in

private theorem rayGammaFactor_real_notMemS (s : ℂ) (w : {w : InfinitePlace K // IsReal w}) (hw : w ∉ S) :
    ((Real.pi * (mult w.1 : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w.1)
        * Complex.Gamma (rayPlaceExp K S s w.1)
      = Gammaℝ s := by
  have hvS : (⟨w.1, w.2⟩ : {w : InfinitePlace K // IsReal w}) ∉ S := by simpa using hw
  rw [rayPlaceExp, dif_pos w.2, if_neg hvS, mult_isReal, Nat.cast_one, Nat.cast_one, mul_one,
    one_mul, add_zero, Gammaℝ_def, neg_div]

omit [NumberField K] in

private theorem rayGammaFactor_complex (s : ℂ) (w : {w : InfinitePlace K // IsComplex w}) :
    ((Real.pi * (mult w.1 : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w.1)
        * Complex.Gamma (rayPlaceExp K S s w.1)
      = Gammaℂ s / 2 := by
  rw [rayPlaceExp, dif_neg (not_isReal_iff_isComplex.mpr w.2), mult_isComplex, Nat.cast_ofNat,
    Nat.cast_ofNat, add_zero, show (2 : ℂ) * (s / 2) = s by ring, Gammaℂ_def,
    mul_comm Real.pi 2]
  push_cast
  ring

private theorem ray_prod_gammaFactor_eq (s : ℂ) :
    ∏ w : InfinitePlace K, (((Real.pi * (mult w : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
        * Complex.Gamma (rayPlaceExp K S s w))
      = Gammaℝ (s + 1) ^ S.card * Gammaℝ s ^ (nrRealPlaces K - S.card)
          * (Gammaℂ s / 2) ^ nrComplexPlaces K := by
  classical
  rw [prod_eq_prod_mul_prod]
  have hC : (∏ w : {w : InfinitePlace K // IsComplex w},
        (((Real.pi * (mult w.1 : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w.1)
          * Complex.Gamma (rayPlaceExp K S s w.1)))
      = (Gammaℂ s / 2) ^ nrComplexPlaces K := by
    rw [Finset.prod_congr rfl (fun w _ => rayGammaFactor_complex K S s w),
      Finset.prod_const, Finset.card_univ]
  have hR : (∏ w : {w : InfinitePlace K // IsReal w},
        (((Real.pi * (mult w.1 : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w.1)
          * Complex.Gamma (rayPlaceExp K S s w.1)))
      = Gammaℝ (s + 1) ^ S.card * Gammaℝ s ^ (nrRealPlaces K - S.card) := by
    rw [← Finset.prod_filter_mul_prod_filter_not
        (Finset.univ : Finset {w : InfinitePlace K // IsReal w}) (· ∈ S),
      Finset.prod_congr rfl (fun w hw => rayGammaFactor_real_memS K S s w
        (Finset.mem_filter.mp hw).2),
      Finset.prod_congr rfl (fun w hw => rayGammaFactor_real_notMemS K S s w
        (Finset.mem_filter.mp hw).2),
      Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [hC, hR]

private theorem sum_rayPlaceExp_eq (s : ℂ) :
    ∑ w : InfinitePlace K, rayPlaceExp K S s w
      = (Module.finrank ℚ K : ℂ) * (s / 2) + S.card * (1 / 2 : ℂ) := by
  classical
  simp only [rayPlaceExp, Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum, sum_mult_eq]
  congr 1
  rw [sum_eq_sum_add_sum (K := K)
    (fun w => if h : IsReal w then (if ⟨w, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0),
    show (∑ w : {w : InfinitePlace K // IsComplex w},
        if h : IsReal w.1 then (if ⟨w.1, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0) = 0 from
      Finset.sum_eq_zero fun w _ => dif_neg (not_isReal_iff_isComplex.mpr w.2),
    add_zero,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset {w : InfinitePlace K // IsReal w})
      (· ∈ S),
    show (∑ w ∈ Finset.filter (¬ · ∈ S) (Finset.univ : Finset {w : InfinitePlace K // IsReal w}),
        if h : IsReal w.1 then (if ⟨w.1, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0) = 0 from
      Finset.sum_eq_zero fun w hw => by
        rw [dif_pos w.2, if_neg (by simpa using (Finset.mem_filter.mp hw).2)],
    add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_congr rfl (fun w hw => by
      rw [dif_pos w.2, if_pos (show (⟨w.1, w.2⟩ : {w : InfinitePlace K // IsReal w}) ∈ S by
        simpa using hw)]),
    Finset.sum_const, nsmul_eq_mul]

private theorem ray_prod_rayScale_cpow (h𝔣 : 𝔣 ≠ ⊥) (s : ℂ) :
    ∏ w : InfinitePlace K, ((rayScale K 𝔣 𝔞 : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
      = ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ)⁻¹ ^ S.card
          * ((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ) : ℂ) ^ (s / 2)
          * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s := by
  set c := rayScale K 𝔣 𝔞 with hcdef
  have hc : 0 < c := rayScale_pos K 𝔣 h𝔣 𝔞
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hN𝔣 : (0 : ℝ) < (Ideal.absNorm 𝔣 : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h𝔣)
  have hA : (0 : ℝ) < |(discr K : ℝ)| := abs_discr_pos K
  have hN𝔞 : (0 : ℝ) < (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    absNorm_units_pos K 𝔞
  have hB : (0 : ℝ) < |(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
      * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 := by positivity
  have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos; positivity
  rw [ray_prod_cpow_eq_cpow_sum _ hc0, Finset.sum_neg_distrib,
    sum_rayPlaceExp_eq K S s, neg_add, Complex.cpow_add _ _ hc0]
  have hS : ((c : ℝ) : ℂ) ^ (-((S.card : ℂ) * (1 / 2)))
      = ((Real.sqrt c : ℝ) : ℂ)⁻¹ ^ S.card := by
    rw [show -((S.card : ℂ) * (1 / 2)) = ((1 / 2 : ℝ) : ℂ) * (-(S.card : ℂ)) by push_cast; ring,
      Complex.cpow_mul_ofReal_nonneg hc.le, ← Real.sqrt_eq_rpow,
      show (-(S.card : ℂ)) = ((-(S.card : ℤ) : ℤ) : ℂ) by push_cast; ring,
      Complex.cpow_intCast, zpow_neg, zpow_natCast, ← inv_pow]
  have hns : ((c : ℝ) : ℂ) ^ (-((Module.finrank ℚ K : ℂ) * (s / 2)))
      = ((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ) : ℂ) ^ (s / 2)
          * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s := by
    rw [hcdef, rayScale, show ∀ z : ℂ, (((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
            * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
          ^ (-(1 : ℝ) / (Module.finrank ℚ K : ℝ)) : ℝ) : ℂ) ^ z
        = ((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)
            * (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 : ℝ) : ℂ)
            ^ (((-(1 : ℝ) / (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * z)
        from fun z => (Complex.cpow_mul_ofReal_nonneg hB.le _ z).symm]
    have hnc : (Module.finrank ℚ K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hexp : (((-(1 : ℝ) / (Module.finrank ℚ K : ℝ) : ℝ) : ℂ))
        * (-((Module.finrank ℚ K : ℂ) * (s / 2))) = s / 2 := by
      push_cast; field_simp
    rw [hexp, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mul_nonneg hA.le hN𝔣.le) (sq_nonneg _),
      ray_pow_cpow_eq_cpow_mul hN𝔞.le 2,
      show ((2 : ℕ) : ℂ) * (s / 2) = s by push_cast; ring]
  rw [hS, hns]; ring

private theorem ray_prod_sq_place_cpow
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) (s : ℂ) :
    ∏ w : InfinitePlace K, (((w (fracIdealGen K 𝔞 I)) ^ 2 : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
      = ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
            * (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) : ℝ) : ℂ) ^ (-s)
          * (∏ v ∈ S, (((v : InfinitePlace K) (fracIdealGen K 𝔞 I) : ℝ) : ℂ))⁻¹ := by
  set g := fracIdealGen K 𝔞 I with hg
  have hg0 : g ≠ 0 := fracIdealGen_ne_zero K 𝔞 I

  have hsplit : ∀ w : InfinitePlace K, (((w g) ^ 2 : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
      = (((w g) ^ 2 : ℝ) : ℂ) ^ (-((mult w : ℂ) * (s / 2)))
          * (((w g) ^ 2 : ℝ) : ℂ)
              ^ (-(if h : IsReal w then (if ⟨w, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0)) := by
    intro w
    have hwg : 0 < w g := pos_iff.mpr hg0
    rw [rayPlaceExp, neg_add, Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hwg.ne'))]
  simp only [hsplit]
  rw [Finset.prod_mul_distrib]
  congr 1
  ·
    rw [Finset.prod_congr rfl (fun w _ => show
          (((w g) ^ 2 : ℝ) : ℂ) ^ (-((mult w : ℂ) * (s / 2)))
            = (((w g) ^ mult w : ℝ) : ℂ) ^ (-s) by
          rw [ray_pow_cpow_eq_cpow_mul (apply_nonneg w g) 2,
            ray_pow_cpow_eq_cpow_mul (apply_nonneg w g) (mult w)]
          congr 1; push_cast; ring),
      ← ray_ofReal_prod_cpow _ _ _ (fun w _ => pow_nonneg (apply_nonneg w g) _),
      prod_pow_mult_fracIdealGen K 𝔞 I]
  ·
    rw [prod_eq_prod_mul_prod,
      show (∏ w : {w : InfinitePlace K // IsComplex w}, (((w.1 g) ^ 2 : ℝ) : ℂ)
            ^ (-(if h : IsReal w.1 then (if ⟨w.1, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0))) = 1
        from Finset.prod_eq_one fun w _ => by
          rw [dif_neg (not_isReal_iff_isComplex.mpr w.2), neg_zero, Complex.cpow_zero],
      mul_one,
      ← Finset.prod_filter_mul_prod_filter_not
        (Finset.univ : Finset {w : InfinitePlace K // IsReal w}) (· ∈ S),
      show (∏ w ∈ Finset.filter (¬ · ∈ S) (Finset.univ : Finset {w : InfinitePlace K // IsReal w}),
          (((w.1 g) ^ 2 : ℝ) : ℂ)
            ^ (-(if h : IsReal w.1 then (if ⟨w.1, h⟩ ∈ S then (1 : ℂ) / 2 else 0) else 0))) = 1
        from Finset.prod_eq_one fun w hw => by
          rw [dif_pos w.2, if_neg (by simpa using (Finset.mem_filter.mp hw).2), neg_zero,
            Complex.cpow_zero],
      mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvg : 0 < (v : InfinitePlace K) g := pos_iff.mpr hg0
    rw [dif_pos v.2,
      if_pos (show (⟨v.1, v.2⟩ : {w : InfinitePlace K // IsReal w}) ∈ S by simpa using hv),
      show -((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) * (-1 : ℂ) by push_cast; ring,
      Complex.cpow_mul_ofReal_nonneg (sq_nonneg _), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hvg.le, Complex.cpow_neg_one]

private theorem ray_stepE_aux {A G1 G2 G3 SC DN NA NI : ℂ} {m : ℕ} (hA : A ≠ 0) (hNA : NA ≠ 0) :
    A * (G1 * G2 * (G3 ^ m / 2 ^ m) * (SC * DN * NA) * (NA⁻¹ * NI * A⁻¹))
      = SC * 2⁻¹ ^ m * (DN * G2 * G1 * G3 ^ m) * NI := by
  have h2 : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero m two_ne_zero
  rw [inv_pow]
  field_simp

private theorem prod_rayPlace_gamma_eq (h𝔣 : 𝔣 ≠ ⊥)
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹}) (s : ℂ) :
    (∏ v ∈ S, (((v : InfinitePlace K) (fracIdealGen K 𝔞 I) : ℝ) : ℂ))
      * ∏ w : InfinitePlace K,
          ((rayPlaceRate K (rayScale K 𝔣 𝔞) (fracIdealGen K 𝔞 I) w : ℝ) : ℂ)
              ^ (-rayPlaceExp K S s w)
            * Complex.Gamma (rayPlaceExp K S s w)
      = rayGammaBlock K 𝔣 S (rayScale K 𝔣 𝔞) s
          * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s) := by
  set g := fracIdealGen K 𝔞 I with hg
  set c := rayScale K 𝔣 𝔞 with hc
  have hc0 : 0 < c := rayScale_pos K 𝔣 h𝔣 𝔞
  have hg0 : g ≠ 0 := fracIdealGen_ne_zero K 𝔞 I

  have hrate : ∀ w, ((rayPlaceRate K c g w : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
      = ((Real.pi * (mult w : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
        * ((c : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
        * (((w g) ^ 2 : ℝ) : ℂ) ^ (-rayPlaceExp K S s w) := fun w => by
    have hπm : 0 ≤ Real.pi * (mult w : ℝ) := by positivity
    rw [show (rayPlaceRate K c g w : ℝ) = (Real.pi * (mult w : ℝ)) * c * (w g) ^ 2 by
        rw [rayPlaceRate]; ring,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (mul_nonneg hπm hc0.le) (sq_nonneg _),
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hπm hc0.le]
  simp only [hrate]
  rw [Finset.prod_congr rfl (fun w _ => show
      ((Real.pi * (mult w : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
        * ((c : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
        * (((w g) ^ 2 : ℝ) : ℂ) ^ (-rayPlaceExp K S s w) * Complex.Gamma (rayPlaceExp K S s w)
      = (((Real.pi * (mult w : ℝ) : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
          * Complex.Gamma (rayPlaceExp K S s w))
        * ((c : ℝ) : ℂ) ^ (-rayPlaceExp K S s w)
        * (((w g) ^ 2 : ℝ) : ℂ) ^ (-rayPlaceExp K S s w) by ring),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]

  rw [ray_prod_gammaFactor_eq K S s, hc, hg, ray_prod_rayScale_cpow K 𝔣 S 𝔞 h𝔣 s,
    ray_prod_sq_place_cpow K S 𝔞 I s, rayGammaBlock]

  rw [← hg]
  have hprodS : (∏ v ∈ S, (((v : InfinitePlace K) g : ℝ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ =>
      Complex.ofReal_ne_zero.mpr (pos_iff.mpr hg0 : (0 : ℝ) < (v : InfinitePlace K) g).ne'
  have hN𝔞c : ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (absNorm_units_pos K 𝔞).ne'
  have hNI : (0 : ℝ) ≤ (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) := Nat.cast_nonneg _

  have hDsplit : ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
        * (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) : ℝ) : ℂ) ^ (-s)
      = ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s)
          * (((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) : ℂ)) ^ (-s) := by
    rw [Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (absNorm_units_pos K 𝔞).le hNI]
  rw [hDsplit,
    show (((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) : ℂ))
        = ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) from by push_cast; rfl,
    Complex.cpow_neg ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) s,
    div_pow]
  exact ray_stepE_aux hprodS (Complex.cpow_ne_zero_iff.mpr (.inl hN𝔞c))

private theorem rayOrbitMellin_fracIdealGen_eq (h𝔣 : 𝔣 ≠ ⊥)
    (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K 𝔞)⁻¹})
    {s : ℂ} (hs : 0 < s.re) :
    rayOrbitMellin K 𝔣 χ S 𝔞 (rayScale K 𝔣 𝔞) (fracIdealGen K 𝔞 I) s
      = rayGammaBlock K 𝔣 S (rayScale K 𝔣 𝔞) s
          * (chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
              * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)) := by
  have hc := rayScale_pos K 𝔣 h𝔣 𝔞
  have hg := fracIdealGen_ne_zero K 𝔞 I
  rw [rayOrbitMellin,
    setIntegral_congr_fun (measurableSet_setOf_pos K) (fun t _ =>
      rayOrbitKernel_fracIdealGen_factored K 𝔣 χ S 𝔞 I (rayScale K 𝔣 𝔞) s t),
    integral_const_mul,
    setIntegral_orthant_rayGaussian_eq_prod K S (rayScale K 𝔣 𝔞) hc hg hs,
    show (chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
          * ∏ v ∈ S, (((v : InfinitePlace K) (fracIdealGen K 𝔞 I) : ℝ) : ℂ))
        * ∏ w : InfinitePlace K,
            ((rayPlaceRate K (rayScale K 𝔣 𝔞) (fracIdealGen K 𝔞 I) w : ℝ) : ℂ)
                ^ (-rayPlaceExp K S s w)
              * Complex.Gamma (rayPlaceExp K S s w)
      = chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
          * ((∏ v ∈ S, (((v : InfinitePlace K) (fracIdealGen K 𝔞 I) : ℝ) : ℂ))
              * ∏ w : InfinitePlace K,
                  ((rayPlaceRate K (rayScale K 𝔣 𝔞) (fracIdealGen K 𝔞 I) w : ℝ) : ℂ)
                      ^ (-rayPlaceExp K S s w)
                    * Complex.Gamma (rayPlaceExp K S s w)) from (mul_assoc _ _ _),
    prod_rayPlace_gamma_eq K 𝔣 S 𝔞 h𝔣 I s]
  ring

private theorem norm_chiIdeal_le_one (h𝔣 : 𝔣 ≠ ⊥) (I : FractionalIdeal (𝓞 K)⁰ K) :
    ‖chiIdeal K 𝔣 χ I‖ ≤ 1 := by
  rcases eq_or_ne I 0 with h | h
  · rw [h, chiIdeal_zero]; simp
  · rcases em (Units.mk0 I h ∈ coprimeToModulus K 𝔣) with hc | hc
    · rw [norm_chiIdeal_of_mem χ h𝔣 h hc]
    · rw [chiIdeal_eq_zero_of_not_mem χ h hc]; simp

private theorem summable_chiIdeal_mul_cpow_of_class (h𝔣 : 𝔣 ≠ ⊥) (C : ClassGroup (𝓞 K))
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
        * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)) := by
  have hbound : ∀ I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
      ‖chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
        * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)‖
      ≤ ‖((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)‖ := fun I => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_chiIdeal_le_one K 𝔣 χ h𝔣 _)
  have hbase := (summable_class_cpow K C hs).norm
  exact (hbase.of_nonneg_of_le (fun _ => norm_nonneg _) hbound).of_norm

private theorem summable_chiIdeal_mul_cpow_total (h𝔣 : 𝔣 ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : (Ideal (𝓞 K))⁰ =>
      chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I)
        * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ^ (-s)) := by
  rw [← (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).summable_iff]
  refine .of_norm ((summable_sigma_of_nonneg fun _ => norm_nonneg _).mpr ⟨?_, ?_⟩)
  · exact fun C => (summable_chiIdeal_mul_cpow_of_class K 𝔣 χ h𝔣 C hs).norm
  · exact Summable.of_finite

private theorem sum_classes_tsum_chiIdeal_eq (h𝔣 : 𝔣 ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K),
        ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
          chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
            * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)
      = ∑' I : (Ideal (𝓞 K))⁰, chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I)
          * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ^ (-s) := by
  have htot := summable_chiIdeal_mul_cpow_total K 𝔣 χ h𝔣 hs
  have hσ : Summable (fun p : Σ C : ClassGroup (𝓞 K), {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C}
      => chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K p.2.1)
        * ((Ideal.absNorm (p.2.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)) :=
    (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).summable_iff.mpr htot
  have hts : (∑' I : (Ideal (𝓞 K))⁰, chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I)
          * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ^ (-s))
      = ∑' C : ClassGroup (𝓞 K),
          ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
            chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
              * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s) :=
    ((Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).tsum_eq
        (fun I => chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I)
          * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ^ (-s))).symm.trans
      (hσ.tsum_sigma' fun C => summable_chiIdeal_mul_cpow_of_class K 𝔣 χ h𝔣 C hs)
  rw [← (hasSum_fintype _).tsum_eq]
  exact hts.symm

private def rayClassSet (C : NarrowRayClassGroup K 𝔣) : Set (Ideal (𝓞 K))⁰ :=
  {I | ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣,
    NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩ = C}

private theorem summable_absNorm_cpow_total {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : (Ideal (𝓞 K))⁰ => ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ^ (-s)) := by
  rw [← (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).summable_iff]
  refine .of_norm ((summable_sigma_of_nonneg fun _ => norm_nonneg _).mpr ⟨?_, ?_⟩)
  · exact fun C => (summable_class_cpow K C hs).norm
  · exact Summable.of_finite

private theorem rayZetaCoeff_zero (C : NarrowRayClassGroup K 𝔣) : rayZetaCoeff K 𝔣 C 0 = 0 := by
  haveI : IsEmpty {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = 0 ∧
      ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣,
        NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩ = C} :=
    ⟨fun I => nonZeroDivisors.coe_ne_zero I.1
      ((Ideal.absNorm_eq_zero_iff.mp I.2.1).trans Ideal.zero_eq_bot.symm)⟩
  rw [rayZetaCoeff]
  exact Nat.card_of_isEmpty

private theorem rayClassSet_cpow_fiber_tsum (C : NarrowRayClassGroup K 𝔣) (s : ℂ) (n : ℕ) :
    ∑' x : (fun I : rayClassSet K 𝔣 C => Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n},
      ((Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)
      = (rayZetaCoeff K 𝔣 C n : ℂ) * ((n : ℂ)) ^ (-s) := by
  classical
  have e : ((fun I : rayClassSet K 𝔣 C => Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n}) ≃
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧
        ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣,
          NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩ = C} :=
    { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧
      ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣,
        NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩ = C} :=
    Set.Finite.to_subtype <|
      (Ideal.finite_setOf_absNorm_le₀ n).subset fun _ hI => le_of_eq hI.1
  haveI : Finite ((fun I : rayClassSet K 𝔣 C => Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n}
      : Set _) := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite ((fun I : rayClassSet K 𝔣 C =>
      Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n} : Set _)
  have hconst : ∀ x : ((fun I : rayClassSet K 𝔣 C =>
      Ideal.absNorm (I.1 : Ideal (𝓞 K))) ⁻¹' {n} : Set _),
      ((Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s) = ((n : ℂ)) ^ (-s) := by
    intro x
    have hx : Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) = n := x.2
    rw [hx]
  rw [tsum_congr hconst, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [rayZetaCoeff, ← Nat.card_eq_fintype_card]
  exact_mod_cast congrArg (Nat.cast (R := ℂ)) (Nat.card_congr e)

private theorem tsum_rayClassSet_cpow_eq_rayZeta (C : NarrowRayClassGroup K 𝔣) {s : ℂ}
    (hs : 1 < s.re) :
    ∑' I : rayClassSet K 𝔣 C, ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)
      = rayZeta K 𝔣 C s := by
  classical
  set ν : rayClassSet K 𝔣 C → ℕ := fun I => Ideal.absNorm (I.1 : Ideal (𝓞 K)) with hν
  have hsum : Summable (fun I : rayClassSet K 𝔣 C =>
      ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)) :=
    (summable_absNorm_cpow_total K hs).subtype _
  have h1 := hsum.hasSum.tsum_fiberwise ν
  have h2 : ∑' n : ℕ, ∑' x : (ν ⁻¹' {n} : Set _),
      ((Ideal.absNorm (x.1.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)
      = ∑' I : rayClassSet K 𝔣 C, ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s) :=
    h1.tsum_eq
  rw [← h2, rayZeta, LSeries]
  refine tsum_congr fun n => ?_
  rw [rayClassSet_cpow_fiber_tsum K 𝔣 C s n]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [LSeries.term, rayZetaCoeff_zero]
  · rw [LSeries.term_of_ne_zero (Nat.pos_iff_ne_zero.mp hn), Complex.cpow_neg,
      div_eq_mul_inv]

private theorem chiIdeal_mul_cpow_eq_sum_indicator [Fintype (NarrowRayClassGroup K 𝔣)]
    (I : (Ideal (𝓞 K))⁰) (s : ℂ) :
    chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I) * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ^ (-s)
      = ∑ C : NarrowRayClassGroup K 𝔣, χ C * (rayClassSet K 𝔣 C).indicator
          (fun J : (Ideal (𝓞 K))⁰ => ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ)) ^ (-s)) I := by
  classical
  have h0 : ((FractionalIdeal.mk0 K I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := (FractionalIdeal.mk0 K I).ne_zero
  have hmk : Units.mk0 _ h0 = FractionalIdeal.mk0 K I := Units.ext rfl
  by_cases hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣
  · have hin : Units.mk0 _ h0 ∈ coprimeToModulus K 𝔣 := by rw [hmk]; exact hc
    have hval : chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I)
        = χ (NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩) := by
      rw [chiIdeal, dif_pos h0, dif_pos hin]
      exact congrArg (χ ∘ NarrowRayClassGroup.mk K 𝔣) (Subtype.ext hmk)
    have hI : I ∈ rayClassSet K 𝔣 (NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩) :=
      ⟨hc, rfl⟩
    rw [hval, Finset.sum_eq_single (NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩),
      Set.indicator_of_mem hI]
    · intro C _ hC
      have hI' : I ∉ rayClassSet K 𝔣 C := fun h => by
        obtain ⟨_, h⟩ := h
        exact hC h.symm
      rw [Set.indicator_of_notMem hI', mul_zero]
    · exact fun h => (h (Finset.mem_univ _)).elim
  · have hI : ∀ C : NarrowRayClassGroup K 𝔣, I ∉ rayClassSet K 𝔣 C := fun C h => by
      obtain ⟨hc', _⟩ := h
      exact hc hc'
    rw [chiIdeal_eq_zero_of_not_mem χ h0 (by rw [hmk]; exact hc), zero_mul]
    exact (Finset.sum_eq_zero fun C _ => by rw [Set.indicator_of_notMem (hI C), mul_zero]).symm

private theorem sum_tsum_chiIdeal_eq_rayClassLSeries {ι : Type} [Fintype ι] (h𝔣 : 𝔣 ≠ ⊥)
    (𝔞' : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞' i))
    {s : ℂ} (hs : 1 < s.re) :
    ∑ i : ι, ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K (𝔞' i))⁻¹},
        chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
          * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)
      = rayClassLSeries K 𝔣 χ s := by
  classical
  haveI : Finite (NarrowRayClassGroup K 𝔣) := finite K h𝔣
  haveI := @Fintype.ofFinite _ (finite K h𝔣)

  have hbij' : Function.Bijective fun i => (ClassGroup.mk K (𝔞' i))⁻¹ :=
    (Function.bijective_iff_existsUnique _).mpr fun C =>
      (hbij.existsUnique C⁻¹).imp fun i ⟨hi, hu⟩ =>
        ⟨inv_eq_iff_eq_inv.mpr hi, fun j hj => hu j (inv_eq_iff_eq_inv.mp hj)⟩
  rw [Fintype.sum_bijective _ hbij' _ (fun C => ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
      chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
        * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)) (fun _ => rfl)]

  have hsumC : ∀ C : ClassGroup (𝓞 K),
      Summable (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
        chiIdeal K 𝔣 χ (FractionalIdeal.mk0 K I.1)
          * ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ)) ^ (-s)) :=
    fun C => summable_chiIdeal_mul_cpow_of_class K 𝔣 χ h𝔣 C hs

  rw [sum_classes_tsum_chiIdeal_eq K 𝔣 χ h𝔣 hs]

  have hker := summable_absNorm_cpow_total K hs
  have hsw : ∀ C ∈ (Finset.univ : Finset (NarrowRayClassGroup K 𝔣)),
      Summable fun I : (Ideal (𝓞 K))⁰ => χ C * (rayClassSet K 𝔣 C).indicator
        (fun J : (Ideal (𝓞 K))⁰ => ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ)) ^ (-s)) I :=
    fun C _ => (hker.indicator _).mul_left (χ C)
  have _ := hsumC
  rw [tsum_congr fun I => chiIdeal_mul_cpow_eq_sum_indicator K 𝔣 χ I s,
    Summable.tsum_finsetSum hsw, rayClassLSeries,
    tsum_fintype (fun C : NarrowRayClassGroup K 𝔣 => χ C * rayZeta K 𝔣 C s)]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [tsum_mul_left, ← tsum_subtype]
  exact congrArg (χ C * ·) (tsum_rayClassSet_cpow_eq_rayZeta K 𝔣 C hs)

end RayTc1
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

private noncomputable def topChiUnitsHom (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ℂ where
  toFun I := χT (NarrowRayClassGroup.mk K ⊤ ⟨I, mem_coprimeToModulus_top K I⟩)
  map_one' := by rw [show (⟨(1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ), mem_coprimeToModulus_top K 1⟩
      : coprimeToModulus K (⊤ : Ideal (𝓞 K))) = 1 from rfl, map_one, map_one]
  map_mul' I J := by
    rw [← map_mul, ← map_mul]
    rfl

private theorem topChiUnitsHom_eq_chiIdeal (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    topChiUnitsHom K χT I = chiIdeal K ⊤ χT (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [chiIdeal, dif_pos I.ne_zero, dif_pos (mem_coprimeToModulus_top K (Units.mk0 _ I.ne_zero))]
  exact congrArg (χT ∘ NarrowRayClassGroup.mk K ⊤) (Subtype.ext (Units.ext rfl))

private theorem topChiUnitsHom_principal (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (hpar : IsParity K ⊤ χT ∅) {α : 𝓞 K} (hα : α ≠ 0) :
    topChiUnitsHom K χT (Units.mk0 (prinFI K α) (prinFI_ne_zero K hα)) = 1 := by
  rw [topChiUnitsHom_eq_chiIdeal, Units.val_mk0]
  exact (hpar α hα Submodule.mem_top).trans (by simp [signAt])

private theorem surjective_classGroup_mk_K : Function.Surjective (ClassGroup.mk K (R := 𝓞 K)) :=
  fun C => ClassGroup.induction K (fun I => ⟨I, rfl⟩) C

private theorem topChiUnitsHom_spanSingleton (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (hpar : IsParity K ⊤ χT ∅) {x : K} (hx : x ≠ 0) :
    topChiUnitsHom K χT (Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)) = 1 := by
  obtain ⟨⟨α, β⟩, hx'⟩ := IsLocalization.surj (𝓞 K)⁰ x
  have hβ0 : β.1 ≠ 0 := nonZeroDivisors.coe_ne_zero β
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx'
    exact hx ((mul_eq_zero.mp hx').resolve_right (RingOfIntegers.coe_ne_zero_iff.mpr hβ0))
  have hkey : Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      * Units.mk0 (prinFI K β.1) (prinFI_ne_zero K hβ0)
      = Units.mk0 (prinFI K α) (prinFI_ne_zero K hα0) := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, prinFI, prinFI,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, hx'])
  have h := congrArg (topChiUnitsHom K χT) hkey
  rw [map_mul, topChiUnitsHom_principal K χT hpar hα0,
    topChiUnitsHom_principal K χT hpar hβ0, mul_one] at h
  exact h

private noncomputable def topChiUnitsHomU (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ℂˣ :=
  (topChiUnitsHom K χT).toHomUnits

private noncomputable def topWideChar (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (hpar : IsParity K ⊤ χT ∅) : ClassGroup (𝓞 K) →* ℂ :=
  (Units.coeHom ℂ).comp <| (ClassGroup.mk K).liftOfSurjective (surjective_classGroup_mk_K K)
    ⟨topChiUnitsHomU K χT, fun I hI => by
      rw [MonoidHom.mem_ker] at hI ⊢
      obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.mp hI
      have hx0 : x ≠ 0 := fun h => Units.ne_zero I (by
        rw [← FractionalIdeal.coeToSubmodule_eq_bot, hx, h, Submodule.span_zero_singleton])
      have hIeq : I = Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0) := Units.ext (by
        rw [Units.val_mk0, ← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton,
          hx])
      refine Units.ext ?_
      unfold topChiUnitsHomU
      rw [hIeq, MonoidHom.coe_toHomUnits,
        topChiUnitsHom_spanSingleton K χT hpar hx0, Units.val_one]⟩

private theorem topWideChar_mk (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (hpar : IsParity K ⊤ χT ∅) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    topWideChar K χT hpar (ClassGroup.mk K I) = topChiUnitsHom K χT I := by
  unfold topWideChar topChiUnitsHomU
  rw [MonoidHom.comp_apply,
    (ClassGroup.mk K).liftOfRightInverse_comp_apply _ _ _ I, Units.coeHom_apply,
    MonoidHom.coe_toHomUnits]

private theorem topWideChar_ne_one (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (hpar : IsParity K ⊤ χT ∅) (hχ : χT ≠ 1) : topWideChar K χT hpar ≠ 1 := by
  intro h1
  refine hχ (MonoidHom.ext fun D => ?_)
  obtain ⟨⟨I, hI⟩, rfl⟩ := QuotientGroup.mk'_surjective _ D
  have := congrFun (congrArg DFunLike.coe h1) (ClassGroup.mk K I)
  rw [topWideChar_mk, MonoidHom.one_apply] at this
  exact this.symm.trans (congrArg (χT ∘ NarrowRayClassGroup.mk K ⊤) (Subtype.ext rfl)) |>.symm
    |>.trans rfl

private theorem uWeight_top_eq_topWideChar_inv (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (hpar : IsParity K ⊤ χT ∅) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ≠ 0) :
    uWeight K ⊤ χT ∅ 𝔞 x = topWideChar K χT hpar (ClassGroup.mk K 𝔞)⁻¹ := by
  rw [uWeight, signAt, Finset.prod_empty, mul_one,
    ← Units.val_mk0 (a := FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx), ← Units.val_mul,
    ← topChiUnitsHom_eq_chiIdeal, map_mul, ← topWideChar_mk K χT hpar, ← topWideChar_mk K χT hpar,
    ← map_inv, ClassGroup.mk_eq_one_iff.mpr
      ⟨x, by rw [Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩,
    map_one, one_mul]

private theorem tc2Alpha_torsionOrder_rayGammaBlock_eq (h𝔣 : 𝔣 ≠ ⊥)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    tc2Alpha K 𝔣 S 𝔞 s * ((torsionOrder K : ℂ) * rayGammaBlock K 𝔣 S (rayScale K 𝔣 𝔞) s)
      = (((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ) : ℂ) ^ (s / 2)
          * Gammaℝ s ^ (nrRealPlaces K - S.card) * Gammaℝ (s + 1) ^ S.card
          * Gammaℂ s ^ nrComplexPlaces K) := by
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_pos K).ne'
  have hc : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  have hsqrt : ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne'
  have h1 : ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ) ^ S.card
      * ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ)⁻¹ ^ S.card = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hsqrt)]
  have h2 : (2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)]
  unfold tc2Alpha tc2Const rayGammaBlock

  rw [show ((2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ)
          * ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ) ^ S.card)
        * ((torsionOrder K : ℂ)
          * (((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ)⁻¹ ^ S.card
              * (2 : ℂ)⁻¹ ^ nrComplexPlaces K
              * ((((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ) : ℂ) ^ (s / 2)
                  * Gammaℝ s ^ (nrRealPlaces K - S.card) * Gammaℝ (s + 1) ^ S.card
                  * Gammaℂ s ^ nrComplexPlaces K))))
      = ((2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) * (torsionOrder K : ℂ))
        * (((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ) ^ S.card
            * ((Real.sqrt (rayScale K 𝔣 𝔞) : ℝ) : ℂ)⁻¹ ^ S.card)
        * (2 : ℂ)⁻¹ ^ nrComplexPlaces K
        * ((((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ) : ℂ) ^ (s / 2)
            * Gammaℝ s ^ (nrRealPlaces K - S.card) * Gammaℝ (s + 1) ^ S.card
            * Gammaℂ s ^ nrComplexPlaces K)) by ring,
    div_mul_cancel₀ _ hw, h1, mul_one, h2, one_mul]

private theorem completedRayL_eq_sum_rayFoldMellin {ι : Type} [Fintype ι] (h𝔣 : 𝔣 ≠ ⊥)
    (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞 i))
    {s : ℂ} (hs : 1 < s.re) :
    completedRayL K 𝔣 χ S s
      = ∑ i : ι, tc2Alpha K 𝔣 S (𝔞 i) s
          * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s := by
  unfold completedRayL
  rw [← sum_tsum_chiIdeal_eq_rayClassLSeries K 𝔣 χ h𝔣 𝔞 hbij hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rayFoldMellin_unfold K 𝔣 χ S (𝔞 i) h𝔣 (rayScale K 𝔣 (𝔞 i)) (rayScale_pos K 𝔣 h𝔣 (𝔞 i)) hs,
    tsum_congr fun I => rayOrbitMellin_fracIdealGen_eq K 𝔣 χ S (𝔞 i) h𝔣 I (one_pos.trans hs),
    tsum_mul_left, ← mul_assoc, ← mul_assoc,
    mul_assoc (tc2Alpha K 𝔣 S (𝔞 i) s) (torsionOrder K : ℂ) (rayGammaBlock K 𝔣 S _ s),
    tc2Alpha_torsionOrder_rayGammaBlock_eq K 𝔣 S h𝔣 (𝔞 i) s]

private theorem uWeight_x0_eq_wideFactor [Fintype (𝓞 K ⧸ 𝔣)] (h𝔣 : 𝔣 ≠ ⊥) (hS : S = ∅)
    (htriv : ∀ α : 𝓞 K, chiFin K 𝔣 χ S α = 0 ∨ chiFin K 𝔣 χ S α = 1) :
    ∃ ψ : ClassGroup (𝓞 K) →* ℂ, (χ ≠ 1 → ψ ≠ 1) ∧
      ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K), IsCoprimeGenerator K 𝔣 χ 𝔞 x₀ →
        uWeight K 𝔣 χ S 𝔞 x₀ = ψ (ClassGroup.mk K 𝔞)⁻¹ := by
  classical
  subst hS

  have hint : ∀ (α : 𝓞 K) (hα : α ≠ 0),
      Units.mk0 ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) (prinFI_ne_zero K hα)
          ∈ coprimeToModulus K 𝔣 →
        chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
    intro α hα hαc
    have hne := chiIdeal_ne_zero_of_mem χ
      (show ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 from
        prinFI_ne_zero K hα) hαc
    rcases htriv α with h | h <;> rw [chiFin, signAt, Finset.prod_empty, mul_one] at h
    · exact absurd h hne
    · exact h

  have hfrac : ∀ (x : K) (hx : x ≠ 0),
      Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) ∈ coprimeToModulus K 𝔣 →
        chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 1 := by
    intro x hx hxc
    have hML := movingLemma K h𝔣
    unfold MovingLemma at hML
    obtain ⟨β, hβ0, hβ1, a, ha⟩ := hML x hx (fun v hv => by
      have h := (mem_coprimeToModulus_iff K).mp hxc v hv
      rwa [Units.val_mk0] at h)
    have hβK : algebraMap (𝓞 K) K β ≠ 0 := fun h =>
      hβ0 (IsFractionRing.injective (𝓞 K) K (h.trans (map_zero (algebraMap (𝓞 K) K)).symm))
    have hβne : ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      prinFI_ne_zero K hβ0
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact mul_ne_zero hβK hx ha.symm
    have hane : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      prinFI_ne_zero K ha0
    have hIa : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
            * FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_mul_spanSingleton, ha]
    have hβc : Units.mk0 ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) hβne
        ∈ coprimeToModulus K 𝔣 := by
      have h := principalUnit_mem_coprimeToModulus K hβ0 hβ1
      rwa [show principalUnit K β hβ0 = Units.mk0 _ hβne from
        Units.ext (principalUnit_val K β hβ0)] at h
    have hac : Units.mk0 ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) hane
        ∈ coprimeToModulus K 𝔣 := by
      rw [show Units.mk0 ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) hane
          = Units.mk0 ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) hβne
            * Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
              (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) from
        Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]; exact hIa)]
      exact mul_mem hβc hxc
    have hmul := chiIdeal_mul_of_mem χ hβne (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      hβc hxc
    rw [← hIa, hint a ha0 hac, hint β hβ0 hβc, one_mul] at hmul
    exact hmul.symm

  have hφ : ∀ y : ↥(coprimeToModulus K 𝔣), χ (NarrowRayClassGroup.mk K 𝔣 y)
      = chiIdeal K 𝔣 χ ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    intro y
    have hc : Units.mk0 ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
        (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero ∈ coprimeToModulus K 𝔣 := by
      rw [show Units.mk0 _ (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero
          = (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) from Units.ext rfl]
      exact y.2
    rw [chiIdeal, dif_pos (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero, dif_pos hc]
    exact congrArg (χ ∘ NarrowRayClassGroup.mk K 𝔣) (Subtype.ext (Units.ext rfl))

  have key : ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K), IsCoprimeGenerator K 𝔣 χ 𝔞 x₀ →
      ∃ y : ↥(coprimeToModulus K 𝔣),
        narrowRayClassGroupToClassGroup K 𝔣 (NarrowRayClassGroup.mk K 𝔣 y)
            = (ClassGroup.mk K 𝔞)⁻¹ ∧
          χ (NarrowRayClassGroup.mk K 𝔣 y)
            = chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
                * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) := by
    intro 𝔞 x₀ hx₀
    have hx0 : x₀ ≠ 0 := by
      intro h0
      apply hx₀.2
      rw [h0, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero]
    have hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0) (𝔞⁻¹).ne_zero
    have hJc : Units.mk0 _ hJ ∈ coprimeToModulus K 𝔣 := by
      by_contra hn
      exact hx₀.2 (chiIdeal_eq_zero_of_not_mem χ hJ hn)
    refine ⟨⟨Units.mk0 _ hJ, hJc⟩, ?_, hφ ⟨Units.mk0 _ hJ, hJc⟩⟩
    rw [narrowRayClassGroupToClassGroup_mk]
    show ClassGroup.mk K (Units.mk0 _ hJ) = (ClassGroup.mk K 𝔞)⁻¹
    rw [show Units.mk0 _ hJ = Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0) * 𝔞⁻¹ from
        Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0]),
      map_mul, map_inv, ClassGroup.mk_eq_one_iff.mpr
        ⟨x₀, by rw [Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩, one_mul]

  have hmk : Function.Surjective (NarrowRayClassGroup.mk K 𝔣) := fun g => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ g
    exact ⟨y, rfl⟩
  have hsurj : Function.Surjective (narrowRayClassGroupToClassGroup K 𝔣) := by
    intro C
    obtain ⟨𝔞, h𝔞⟩ := surjective_classGroup_mk_K K C⁻¹
    obtain ⟨x₀, hx₀⟩ := exists_isCoprimeGenerator K 𝔣 χ 𝔞 h𝔣
    obtain ⟨y, hy, -⟩ := key 𝔞 x₀ hx₀
    exact ⟨NarrowRayClassGroup.mk K 𝔣 y, by rw [hy, h𝔞, inv_inv]⟩
  have hker : (narrowRayClassGroupToClassGroup K 𝔣).ker ≤ χ.toHomUnits.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    obtain ⟨y, rfl⟩ := hmk g
    rw [narrowRayClassGroupToClassGroup_mk, toClassGroup, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype] at hg
    obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.mp hg
    have hx0 : x ≠ 0 := fun h => Units.ne_zero (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (by
      rw [← FractionalIdeal.coeToSubmodule_eq_bot, hx, h, Submodule.span_zero_singleton])
    have hyeq : (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
        = Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
            (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0) := Units.ext (by
      rw [Units.val_mk0, ← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton,
        hx])
    have hxc : Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0) ∈ coprimeToModulus K 𝔣 :=
      hyeq ▸ y.2
    refine Units.ext ?_
    rw [MonoidHom.coe_toHomUnits, Units.val_one, hφ y, hyeq, Units.val_mk0]
    exact hfrac x hx0 hxc

  obtain ⟨ψ, hψ⟩ : ∃ ψ : ClassGroup (𝓞 K) →* ℂ,
      ∀ g, ψ (narrowRayClassGroupToClassGroup K 𝔣 g) = χ g :=
    ⟨(Units.coeHom ℂ).comp
        ((narrowRayClassGroupToClassGroup K 𝔣).liftOfSurjective hsurj ⟨χ.toHomUnits, hker⟩),
      fun g => by
        rw [MonoidHom.comp_apply,
          (narrowRayClassGroupToClassGroup K 𝔣).liftOfRightInverse_comp_apply _ _ _ g,
          Units.coeHom_apply, MonoidHom.coe_toHomUnits]⟩
  refine ⟨ψ, fun hχ hψ1 => hχ (MonoidHom.ext fun g => ?_), fun 𝔞 x₀ hx₀ => ?_⟩
  · rw [MonoidHom.one_apply, ← hψ g, hψ1, MonoidHom.one_apply]
  · obtain ⟨y, hy, hyχ⟩ := key 𝔞 x₀ hx₀
    rw [uWeight, signAt, Finset.prod_empty, mul_one, ← hyχ, ← hψ, hy]

private theorem tc2Cancel {ι : Type} [Fintype ι] [Fintype (𝓞 K ⧸ 𝔣)] (hpar : IsParity K 𝔣 χ S)
    (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
    (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞 i))
    (x₀ : ι → K)
    (hx₀ : ∀ i, IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i))
    (hχ : χ ≠ 1) (s : ℂ) :
    ∑ i : ι, tc2Alpha K 𝔣 S (𝔞 i) s
        * ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a))
          * rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i)) = 0 := by
  by_cases hS : S = ∅
  ·
    by_cases htriv : ∀ α : 𝓞 K, chiFin K 𝔣 χ S α = 0 ∨ chiFin K 𝔣 χ S α = 1
    ·

      obtain ⟨ψ, hψne, hψeq⟩ := uWeight_x0_eq_wideFactor K 𝔣 χ S h𝔣 hS htriv

      have hα : ∀ i, tc2Alpha K 𝔣 S (𝔞 i) s = tc2Const K := fun i => by
        simp only [tc2Alpha, hS, Finset.card_empty, pow_zero, mul_one]
      have hterm : ∀ i, tc2Alpha K 𝔣 S (𝔞 i) s
            * ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a))
              * rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))
          = (tc2Const K * (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a))
              * ((Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))⁻¹) * ψ (ClassGroup.mk K (𝔞 i))⁻¹ := by
        intro i
        rw [hα i, rayInvPolarCoeff_eq K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) hS, hψeq (𝔞 i) (x₀ i) (hx₀ i)]
        ring

      have hbij' : Function.Bijective fun i => (ClassGroup.mk K (𝔞 i))⁻¹ :=
        (Function.bijective_iff_existsUnique _).mpr fun C =>
          (hbij.existsUnique C⁻¹).imp fun i ⟨hi, hu⟩ =>
            ⟨inv_eq_iff_eq_inv.mpr hi, fun j hj => hu j (inv_eq_iff_eq_inv.mp hj)⟩
      have hsum0 : ∑ i : ι, ψ (ClassGroup.mk K (𝔞 i))⁻¹ = 0 := by
        rw [Fintype.sum_bijective _ hbij' _ (ψ ·) (fun _ => rfl)]
        exact sum_hom_units_eq_zero ψ (hψne hχ)
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, hsum0, mul_zero]
    ·
      simp only [not_forall, not_or] at htriv
      obtain ⟨α, hα⟩ := htriv
      rw [ChiFinOrth.sum_chiFin_out_eq_zero K χ S hpar h𝔣' ⟨α, hα⟩]
      simp
  ·
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [rayInvPolarCoeff_eq_zero_of_ne_empty K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) hS, mul_zero, mul_zero]

section TopSlice

variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private noncomputable def topInvDual (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x₀ : K) (s : ℂ) (t : realSpace K) : ℂ :=
  rayInvConst K ⊤ χ S 𝔞 top_ne_bot x₀ * rayMellinWeight K S (1 - s) t
    * ∑' z : {z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
        (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
          * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
              * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ)

private noncomputable def topInvPolar0 (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ :=
  -(if S = ∅ then uWeight K ⊤ χ S 𝔞 1 else 0)

private theorem topChiUnitsHom_spanSingleton_eq_signAt (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K ⊤ χT S) {x : K} (hx : x ≠ 0) :
    topChiUnitsHom K χT (Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)) = signAt K S x := by
  obtain ⟨⟨α, β⟩, hx'⟩ := IsLocalization.surj (𝓞 K)⁰ x
  have hβ0 : β.1 ≠ 0 := nonZeroDivisors.coe_ne_zero β
  have hβK : ((β.1 : 𝓞 K) : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hβ0
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx'
    exact hx ((mul_eq_zero.mp hx').resolve_right hβK)
  have hxβ : x * ((β.1 : 𝓞 K) : K) = ((α : 𝓞 K) : K) := hx'
  have hkey : Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      * Units.mk0 (prinFI K β.1) (prinFI_ne_zero K hβ0)
      = Units.mk0 (prinFI K α) (prinFI_ne_zero K hα0) := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, prinFI, prinFI,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, hxβ])
  have hTα : topChiUnitsHom K χT (Units.mk0 (prinFI K α) (prinFI_ne_zero K hα0))
      = signAt K S ((α : 𝓞 K) : K) := by
    rw [topChiUnitsHom_eq_chiIdeal, Units.val_mk0]
    exact hpar α hα0 Submodule.mem_top
  have hTβ : topChiUnitsHom K χT (Units.mk0 (prinFI K β.1) (prinFI_ne_zero K hβ0))
      = signAt K S ((β.1 : 𝓞 K) : K) := by
    rw [topChiUnitsHom_eq_chiIdeal, Units.val_mk0]
    exact hpar β.1 hβ0 Submodule.mem_top
  have h := congrArg (topChiUnitsHom K χT) hkey
  rw [map_mul, hTα, hTβ, ← hxβ, signAt_mul] at h
  have hββ := signAt_mul_self S hβK
  calc topChiUnitsHom K χT (Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx))
      = topChiUnitsHom K χT (Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx))
          * (signAt K S ((β.1 : 𝓞 K) : K) * signAt K S ((β.1 : 𝓞 K) : K)) := by
        rw [hββ, mul_one]
    _ = (signAt K S x * signAt K S ((β.1 : 𝓞 K) : K)) * signAt K S ((β.1 : 𝓞 K) : K) := by
        rw [← mul_assoc, h]
    _ = signAt K S x := by rw [mul_assoc, hββ, mul_one]

private theorem uWeight_top_of_ne_zero (χT : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K ⊤ χT S)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ≠ 0) :
    uWeight K ⊤ χT S 𝔞 x = topChiUnitsHom K χT 𝔞⁻¹ := by
  rw [uWeight, show FractionalIdeal.spanSingleton (𝓞 K)⁰ x
        * ((𝔞⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = ((Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) * 𝔞⁻¹
            : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) by
        rw [Units.val_mul, Units.val_mk0],
    ← topChiUnitsHom_eq_chiIdeal, map_mul, topChiUnitsHom_spanSingleton_eq_signAt K χT S hpar hx,
    mul_comm (signAt K S x), mul_assoc, signAt_mul_self S hx, mul_one]

private theorem uWeight_apply_zero : uWeight K 𝔣 χ S 𝔞 0 = 0 := by
  rw [uWeight, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero, zero_mul]

private theorem norm_uWeight_le_norm_rayWeight' (x : K) :
    ‖uWeight K 𝔣 χ S 𝔞 x‖ ≤ ‖rayWeight K 𝔣 χ 𝔞 x‖ := by
  by_cases hx : x = 0
  · subst hx
    rw [uWeight_apply_zero, norm_zero]
    exact norm_nonneg _
  · rw [uWeight, rayWeight, if_neg hx, norm_mul]
    by_cases hs : signAt K S x = 0
    · rw [hs, norm_zero, mul_zero]
      exact norm_nonneg _
    · have h1 : ‖signAt K S x‖ = 1 := by
        have h := normSq_signAt (K := K) S hx
        rw [Complex.normSq_eq_norm_sq] at h
        nlinarith [norm_nonneg (signAt K S x)]
      rw [h1, mul_one]

private theorem rayFoldSummand_summable' (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) :
    Summable fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      rayFoldSummand K 𝔣 χ S 𝔞 c t' (x : K) := by
  classical
  set m := Finset.univ.inf' Finset.univ_nonempty t' with hmdef
  have hm : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff]
    exact fun w _ => ht' w
  have hrs : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  have ht₀ : 0 < c * m / rayScale K 𝔣 𝔞 := by positivity
  have hdiag : Summable fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      ‖rayWeight K 𝔣 χ 𝔞 (x : K)
        * (((∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K))
            * Real.exp (-π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞)
                * heckeForm K (x : K)) : ℝ) : ℂ)‖ :=
    summable_norm_iff.mpr (raySummand_summable K 𝔣 χ S 𝔞 h𝔣 ht₀)
  refine Summable.of_norm_bounded
    (g := fun x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
      ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ : ℝ) ^ S.card
        * ‖rayWeight K 𝔣 χ 𝔞 (x : K)
            * (((∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K))
                * Real.exp (-π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞)
                    * heckeForm K (x : K)) : ℝ) : ℂ)‖)
    (hdiag.mul_left _) ?_
  intro x
  have hexp : Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))
      ≤ Real.exp (-π * c * (m * heckeForm K (x : K))) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 := inf_mul_heckeForm_le_torusForm K ht' (x : K)
    rw [← hmdef] at h1
    have h2 : (0 : ℝ) < π * c := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2.le
    nlinarith [h3]
  rw [rayFoldSummand, norm_mul, norm_mul]
  have hnp : ‖(∏ v ∈ S, ((embedding_of_isReal v.2 (x : K) : ℝ) : ℂ))‖
      = ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K) := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun v _ => by
      rw [Complex.norm_real, norm_embedding_of_isReal]
  have hge : ‖(((Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))) : ℝ) : ℂ)‖
      = Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K))) := by
    rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  have hrw : ‖(((∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K))
        * Real.exp (-π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞)
            * heckeForm K (x : K)) : ℝ) : ℂ)‖
      = (Real.sqrt (rayScale K 𝔣 𝔞) ^ S.card * ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
          * Real.exp (-π * c * (m * heckeForm K (x : K))) := by
    have hprodnn : (0 : ℝ) ≤ ∏ v ∈ S, Real.sqrt (rayScale K 𝔣 𝔞) * v.1 (x : K) :=
      Finset.prod_nonneg fun v _ => mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp,
      abs_of_nonneg hprodnn, Finset.prod_mul_distrib, Finset.prod_const,
      show -π * rayScale K 𝔣 𝔞 * (c * m / rayScale K 𝔣 𝔞) * heckeForm K (x : K)
          = -π * c * (m * heckeForm K (x : K)) by field_simp; try ring]
  rw [hnp, hge, norm_mul, hrw]
  have hu := norm_uWeight_le_norm_rayWeight' K 𝔣 χ S 𝔞 (x : K)
  have hprodnn2 : (0:ℝ) ≤ ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K) :=
    Finset.prod_nonneg fun v _ => apply_nonneg _ _
  have hsrs0 : Real.sqrt (rayScale K 𝔣 𝔞) ≠ 0 := (Real.sqrt_pos.mpr hrs).ne'
  have hgoal : ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ : ℝ) ^ S.card
      * (‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
        * ((Real.sqrt (rayScale K 𝔣 𝔞) ^ S.card * ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * (m * heckeForm K (x : K)))))
      = ‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
          * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * (m * heckeForm K (x : K)))) := by
    rw [show ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ : ℝ) ^ S.card
        * (‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
          * ((Real.sqrt (rayScale K 𝔣 𝔞) ^ S.card * ∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
              * Real.exp (-π * c * (m * heckeForm K (x : K)))))
        = ((Real.sqrt (rayScale K 𝔣 𝔞))⁻¹ * Real.sqrt (rayScale K 𝔣 𝔞)) ^ S.card
            * (‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
              * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
                * Real.exp (-π * c * (m * heckeForm K (x : K))))) by rw [mul_pow]; ring,
      inv_mul_cancel₀ hsrs0, one_pow, one_mul]
  rw [hgoal]
  calc ‖uWeight K 𝔣 χ S 𝔞 (x : K)‖ * (∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
        * Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))
      = ‖uWeight K 𝔣 χ S 𝔞 (x : K)‖
          * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * torusForm K t' (mixedEmbedding K (x : K)))) := by ring
    _ ≤ ‖rayWeight K 𝔣 χ 𝔞 (x : K)‖
          * ((∏ v ∈ S, (v.1 : InfinitePlace K) (x : K))
            * Real.exp (-π * c * (m * heckeForm K (x : K)))) :=
        mul_le_mul hu (mul_le_mul_of_nonneg_left hexp hprodnn2) (by positivity) (norm_nonneg _)

private def topIdealLatticeEquiv (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≃ ↥(dilRayLattice K ⊤ 𝔞 top_ne_bot) :=
  (Equiv.subtypeEquivRight (fun y => by
      rw [coe_rayModIdeal, FractionalIdeal.coeIdeal_top, one_mul]
      : ∀ y : K, y ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
        ↔ y ∈ ((rayModIdeal K ⊤ 𝔞 top_ne_bot : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
          : FractionalIdeal (𝓞 K)⁰ K))).trans
    (dilIdealEquiv K (rayModIdeal K ⊤ 𝔞 top_ne_bot))

private theorem topIdealLatticeEquiv_apply (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    ((topIdealLatticeEquiv K 𝔞 y : ↥(dilRayLattice K ⊤ 𝔞 top_ne_bot)) : euclidean.mixedSpace K)
      = dilEmbed K (y : K) := rfl

private theorem summable_top_dual_series (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) :
    Summable fun z : ↥((rayDualIdeal K ⊤ top_ne_bot 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
        : FractionalIdeal (𝓞 K)⁰ K) =>
      polyS (realUnit K) S
          ((placeScale K (rayFlatScaleVec K c t')
              (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)))
        * gaussFT 1
            ((placeScale K (rayFlatScaleVec K c t')
                (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K))) := by
  classical
  have h := phase_oddGaussian_summable (realUnit K)
    (scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
      (mixedDilLattice K (euclideanIdealLattice K (rayModIdeal K ⊤ 𝔞 top_ne_bot))))
    (orthonormal_realUnit K) (0 : euclidean.mixedSpace K) one_pos S
  have h2 := (Equiv.summable_iff (rayDualTransportEquiv K ⊤ 𝔞 top_ne_bot hc ht')).mpr h
  refine h2.congr fun z => ?_
  rw [Function.comp_apply, rayDualTransportEquiv_apply K ⊤ 𝔞 top_ne_bot hc ht' z,
    inner_zero_left, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

private theorem tsum_oddGaussian_top_eq_dual (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℝ} (hc : 0 < c)
    {t' : realSpace K} (ht' : ∀ w, 0 < t' w) :
    (∑' v' : scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
          (dilRayLattice K ⊤ 𝔞 top_ne_bot),
        oddGaussian (realUnit K) 1 S (v' : euclidean.mixedSpace K))
      = (ZLattice.covolume (scaleLattice K (rayFlatScaleVec K c t')
            (rayFlatScaleVec_pos K hc ht') (dilRayLattice K ⊤ 𝔞 top_ne_bot)) volume : ℂ)⁻¹
          * (-Complex.I) ^ S.card
          * ∑' z : ↥((rayDualIdeal K ⊤ top_ne_bot 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
                : FractionalIdeal (𝓞 K)⁰ K),
              (polyS (realUnit K) S
                  ((placeScale K (rayFlatScaleVec K c t')
                      (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)))
                * gaussFT 1
                    ((placeScale K (rayFlatScaleVec K c t')
                        (rayFlatScaleVec_pos K hc ht')).symm (dualPt K (z : K)))) := by
  classical
  haveI : DiscreteTopology (dilRayLattice K ⊤ 𝔞 top_ne_bot) :=
    inferInstanceAs (DiscreteTopology (dilLattice K (rayModIdeal K ⊤ 𝔞 top_ne_bot)))
  haveI : IsZLattice ℝ (dilRayLattice K ⊤ 𝔞 top_ne_bot) :=
    inferInstanceAs (IsZLattice ℝ (dilLattice K (rayModIdeal K ⊤ 𝔞 top_ne_bot)))
  have hP := oddTranslatedTheta_poisson (realUnit K)
    (scaleLattice K (rayFlatScaleVec K c t') (rayFlatScaleVec_pos K hc ht')
      (dilRayLattice K ⊤ 𝔞 top_ne_bot))
    (orthonormal_realUnit K) one_pos S (0 : euclidean.mixedSpace K)
  simp only [add_zero, inner_zero_left, AddChar.map_zero_eq_one, Circle.coe_one, one_mul] at hP
  rw [hP, show (1 / ((1 : ℝ) : ℂ)) ^ S.card = 1 by norm_num, mul_one]
  congr 1
  refine ((Equiv.tsum_eq (rayDualTransportEquiv K ⊤ 𝔞 top_ne_bot hc ht') _).symm).trans
    (tsum_congr fun z => ?_)
  rw [rayDualTransportEquiv_apply K ⊤ 𝔞 top_ne_bot hc ht' z]

private theorem rayFoldMellinIntegrand_inv_top (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K ⊤ χ S)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x₀ : K} (hx₀ : IsCoprimeGenerator K ⊤ χ 𝔞 x₀)
    {t : realSpace K} (ht : t ∈ orthant K) (s : ℂ) :
    rayFoldMellinIntegrand K ⊤ χ S 𝔞 (rayScale K ⊤ 𝔞) s t⁻¹
      = topInvDual K χ S 𝔞 x₀ s t
        + rayInvPolarCoeff K ⊤ χ S 𝔞 top_ne_bot x₀ * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
        + topInvPolar0 K χ S 𝔞 * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2) := by
  classical
  have htw : ∀ w, 0 < t w := ht
  have hti : ∀ w, 0 < t⁻¹ w := fun w => by
    rw [Pi.inv_apply]
    exact inv_pos.mpr (htw w)
  have hc : 0 < rayScale K ⊤ 𝔞 := rayScale_pos K ⊤ top_ne_bot 𝔞
  haveI : DiscreteTopology (dilRayLattice K ⊤ 𝔞 top_ne_bot) :=
    inferInstanceAs (DiscreteTopology (dilLattice K (rayModIdeal K ⊤ 𝔞 top_ne_bot)))
  haveI : IsZLattice ℝ (dilRayLattice K ⊤ 𝔞 top_ne_bot) :=
    inferInstanceAs (IsZLattice ℝ (dilLattice K (rayModIdeal K ⊤ 𝔞 top_ne_bot)))
  have hx₀ne : x₀ ≠ 0 := by
    intro h0
    apply hx₀.2
    rw [h0, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero]
  have hUx : ∀ x : K, x ≠ 0 → uWeight K ⊤ χ S 𝔞 x = uWeight K ⊤ χ S 𝔞 x₀ := fun x hx => by
    rw [uWeight_top_of_ne_zero K χ S hpar 𝔞 hx, uWeight_top_of_ne_zero K χ S hpar 𝔞 hx₀ne]

  have hg0 : (∏ v ∈ S, ((embedding_of_isReal v.2 (0 : K) : ℝ) : ℂ))
        * ((Real.exp (-π * rayScale K ⊤ 𝔞 * torusForm K t⁻¹ (mixedEmbedding K (0 : K))) : ℝ) : ℂ)
      = polyS (realUnit K) S 0 := by
    rw [show (∏ v ∈ S, ((embedding_of_isReal v.2 (0 : K) : ℝ) : ℂ)) = polyS (realUnit K) S 0 by
        rw [polyS_realUnit]
        refine Finset.prod_congr rfl fun v _ => ?_
        simp [map_zero],
      map_zero, show torusForm K t⁻¹ (0 : mixedSpace K) = 0 by simp [torusForm],
      mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one]
  have hA : (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
        rayFoldSummand K ⊤ χ S 𝔞 (rayScale K ⊤ 𝔞) t⁻¹ (x : K))
      = uWeight K ⊤ χ S 𝔞 x₀
          * (∑' v : dilRayLattice K ⊤ 𝔞 top_ne_bot,
              polyS (realUnit K) S (v : euclidean.mixedSpace K)
                * ((Real.exp (-π * rayScale K ⊤ 𝔞 * rayDilForm K t⁻¹
                    (v : euclidean.mixedSpace K)) : ℝ) : ℂ))
        - uWeight K ⊤ χ S 𝔞 x₀ * polyS (realUnit K) S 0 := by
    have hsum := rayFoldSummand_summable' K ⊤ χ S 𝔞 top_ne_bot hc hti
    have hh : HasSum (fun x : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
        if x = (⟨0, FractionalIdeal.zero_mem _⟩ : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)) then uWeight K ⊤ χ S 𝔞 x₀ * polyS (realUnit K) S 0 else 0)
        (uWeight K ⊤ χ S 𝔞 x₀ * polyS (realUnit K) S 0) := hasSum_ite_eq (⟨0, FractionalIdeal.zero_mem _⟩ : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)) _
    have hpt : ∀ x : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K),
        rayFoldSummand K ⊤ χ S 𝔞 (rayScale K ⊤ 𝔞) t⁻¹ (x : K)
          + (if x = (⟨0, FractionalIdeal.zero_mem _⟩ : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)) then uWeight K ⊤ χ S 𝔞 x₀ * polyS (realUnit K) S 0 else 0)
        = uWeight K ⊤ χ S 𝔞 x₀
            * ((∏ v ∈ S, ((embedding_of_isReal v.2 (x : K) : ℝ) : ℂ))
              * ((Real.exp (-π * rayScale K ⊤ 𝔞
                  * torusForm K t⁻¹ (mixedEmbedding K (x : K))) : ℝ) : ℂ)) := by
      intro x
      by_cases hx : x = (⟨0, FractionalIdeal.zero_mem _⟩ : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K))
      · rw [if_pos hx, hx, show ((⟨0, FractionalIdeal.zero_mem _⟩ : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)) : K) = 0 from rfl,
          rayFoldSummand, uWeight_apply_zero, zero_mul, zero_mul, zero_add, hg0]
      · have hxK : (x : K) ≠ 0 := fun h0 => hx (Subtype.ext h0)
        rw [if_neg hx, add_zero, rayFoldSummand, hUx _ hxK, mul_assoc]
    have hT := Equiv.tsum_eq (topIdealLatticeEquiv K 𝔞)
      (fun v : ↥(dilRayLattice K ⊤ 𝔞 top_ne_bot) =>
        polyS (realUnit K) S (v : euclidean.mixedSpace K)
          * ((Real.exp (-π * rayScale K ⊤ 𝔞 * rayDilForm K t⁻¹
              (v : euclidean.mixedSpace K)) : ℝ) : ℂ))
    simp only [topIdealLatticeEquiv_apply, polyS_realUnit_dilEmbed, rayDilForm_dilEmbed] at hT
    calc (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
            rayFoldSummand K ⊤ χ S 𝔞 (rayScale K ⊤ 𝔞) t⁻¹ (x : K))
        = (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
            (rayFoldSummand K ⊤ χ S 𝔞 (rayScale K ⊤ 𝔞) t⁻¹ (x : K)
              + (if x = (⟨0, FractionalIdeal.zero_mem _⟩ : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K)) then uWeight K ⊤ χ S 𝔞 x₀ * polyS (realUnit K) S 0 else 0)))
            - uWeight K ⊤ χ S 𝔞 x₀ * polyS (realUnit K) S 0 := by
          rw [hsum.tsum_add hh.summable, hh.tsum_eq, add_sub_cancel_right]
      _ = uWeight K ⊤ χ S 𝔞 x₀
            * (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K),
                (∏ v ∈ S, ((embedding_of_isReal v.2 (x : K) : ℝ) : ℂ))
                  * ((Real.exp (-π * rayScale K ⊤ 𝔞
                      * torusForm K t⁻¹ (mixedEmbedding K (x : K))) : ℝ) : ℂ))
            - uWeight K ⊤ χ S 𝔞 x₀ * polyS (realUnit K) S 0 := by
          rw [tsum_congr hpt, tsum_mul_left]
      _ = _ := by rw [hT]

  rw [rayFoldMellinIntegrand, hA]
  have hB := tsum_dil_eq_scaled_oddGaussian K ⊤ S 𝔞 top_ne_bot hc hti (0 : euclidean.mixedSpace K)
  simp only [add_zero, map_zero] at hB
  rw [hB, tsum_oddGaussian_top_eq_dual K S 𝔞 hc hti]

  have heval : ∀ z : ↥((rayDualIdeal K ⊤ top_ne_bot 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      : FractionalIdeal (𝓞 K)⁰ K),
      polyS (realUnit K) S ((placeScale K (rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹)
            (rayFlatScaleVec_pos K hc hti)).symm (dualPt K (z : K)))
        * gaussFT 1 ((placeScale K (rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹)
            (rayFlatScaleVec_pos K hc hti)).symm (dualPt K (z : K)))
      = ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
          * ((∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
                * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ)) := fun z => by
    rw [polyS_realUnit_placeScale_symm, polyS_realUnit_dualPt,
      gaussFT_one_placeScale_symm_flat K hc hti (dualPt K (z : K)), inv_inv,
      rayDilForm_dualPt]
    ring
  simp only [heval]
  rw [tsum_mul_left]

  have hCF0 : ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (inv_ne_zero ?_)
    exact (Finset.prod_pos fun v _ => rayFlatScaleVec_pos K hc hti v.1).ne'
  have hsumF : Summable fun z : ↥((rayDualIdeal K ⊤ top_ne_bot 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      : FractionalIdeal (𝓞 K)⁰ K) =>
      (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
        * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
            * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ) := by
    have h1 := (summable_top_dual_series K S 𝔞 hc hti).congr heval
    have h2 := h1.mul_left (((((∏ v ∈ S, rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹
        : ℝ)) : ℂ))⁻¹
    refine h2.congr fun z => ?_
    rw [← mul_assoc, inv_mul_cancel₀ hCF0, one_mul]
  rw [hsumF.tsum_eq_add_tsum_ite ⟨0, FractionalIdeal.zero_mem _⟩]

  rw [show (∏ v ∈ S, ((embedding_of_isReal v.2 (((⟨0, FractionalIdeal.zero_mem _⟩
          : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K))) : K) : ℝ) : ℂ))
      * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
          * torusForm K t (mixedEmbedding K (((⟨0, FractionalIdeal.zero_mem _⟩
              : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K))) : K))) : ℝ) : ℂ)
      = polyS (realUnit K) S 0 by
    rw [show (((⟨0, FractionalIdeal.zero_mem _⟩
          : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K))) : K) = (0 : K) from rfl,
      show (∏ v ∈ S, ((embedding_of_isReal v.2 (0 : K) : ℝ) : ℂ)) = polyS (realUnit K) S 0 by
        rw [polyS_realUnit]
        refine Finset.prod_congr rfl fun v _ => ?_
        simp [map_zero],
      map_zero, show torusForm K t (0 : mixedSpace K) = 0 by simp [torusForm],
      mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one]]

  rw [show (∑' z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K),
      if z = (⟨0, FractionalIdeal.zero_mem _⟩
          : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K)) then (0 : ℂ) else
        (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
          * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
              * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ))
      = ∑' z : {z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ) by
    refine ((tsum_subtype_eq_of_support_subset
        (f := fun z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K) =>
          if z = (⟨0, FractionalIdeal.zero_mem _⟩
              : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K)) then (0 : ℂ) else
            (∏ v ∈ S, ((embedding_of_isReal v.2 (z : K) : ℝ) : ℂ))
              * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
                  * torusForm K t (mixedEmbedding K (z : K))) : ℝ) : ℂ))
        (s := {z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K) | (z : K) ≠ 0})
        ?_).symm).trans (tsum_congr fun z => ?_)
    · intro z hz
      by_contra h0
      simp only [Set.mem_setOf_eq, not_not] at h0
      exact hz (if_pos (Subtype.ext h0))
    · have hz2 : (z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K))
          ≠ ⟨0, FractionalIdeal.zero_mem _⟩ := fun h0 => z.2 (by simp [h0])
      exact if_neg hz2]

  rw [topInvDual, rayInvPolarCoeff, rayInvConst, topInvPolar0, hUx 1 one_ne_zero, neg_div,
    rayMellinWeight, rayMellinWeight, gaussFT_zero_eq_inv_sqrt_pow K hc]

  rw [show ZLattice.covolume (scaleLattice K (rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹)
        (rayFlatScaleVec_pos K hc hti) (dilRayLattice K ⊤ 𝔞 top_ne_bot)) volume
      = Real.sqrt (rayScale K ⊤ 𝔞 ^ Module.finrank ℚ K * torusNorm K t⁻¹)
          * ZLattice.covolume (dilRayLattice K ⊤ 𝔞 top_ne_bot) volume by
    rw [covolume_scaleLattice, prod_rayFlatScaleVec_pow_mult K hc hti]]

  rw [Complex.ofReal_mul, mul_inv]
  rw [show Real.sqrt (rayScale K ⊤ 𝔞 ^ Module.finrank ℚ K * torusNorm K t⁻¹)
      = Real.sqrt (rayScale K ⊤ 𝔞 ^ Module.finrank ℚ K) * (Real.sqrt (torusNorm K t))⁻¹ by
    rw [Real.sqrt_mul (pow_nonneg hc.le _), torusNorm_inv, Real.sqrt_inv],
    Complex.ofReal_mul, mul_inv,
    show ((((Real.sqrt (torusNorm K t))⁻¹ : ℝ)) : ℂ)
        = (((Real.sqrt (torusNorm K t) : ℝ) : ℂ))⁻¹ from Complex.ofReal_inv _,
    inv_inv,
    show ((((Real.sqrt (rayScale K ⊤ 𝔞 ^ Module.finrank ℚ K))⁻¹ : ℝ)) : ℂ)
        = (((Real.sqrt (rayScale K ⊤ 𝔞 ^ Module.finrank ℚ K) : ℝ) : ℂ))⁻¹ from
      Complex.ofReal_inv _]
  have htN : 0 < torusNorm K t := torusNorm_pos K htw
  have htN0 : ((torusNorm K t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htN.ne'
  have harg : ((torusNorm K t : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg htN.le]
    exact Real.pi_ne_zero.symm
  rw [show ((torusNorm K t⁻¹ : ℝ) : ℂ) = (((torusNorm K t : ℝ) : ℂ))⁻¹ by
      rw [torusNorm_inv, Complex.ofReal_inv],
    Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  rw [show ((Real.sqrt (torusNorm K t) : ℝ) : ℂ)
      = ((torusNorm K t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ) by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow htN.le]]
  rw [show ((1 : ℂ) - s) / 2 = (((1 / 2 : ℝ) : ℝ) : ℂ) + -(s / 2) by push_cast; ring,
    Complex.cpow_add _ _ htN0]
  have hSW : raySWeight K S t⁻¹ = (raySWeight K S t)⁻¹ := by
    rw [raySWeight, raySWeight, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Pi.inv_apply, Real.sqrt_inv, Complex.ofReal_inv]
  rw [hSW]

  have hplace : ∀ v : {w : InfinitePlace K // IsReal w},
      (rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹
        * (rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹
      = (rayScale K ⊤ 𝔞)⁻¹ * (Real.sqrt (t v.1) * Real.sqrt (t v.1)) := fun v => by
    have h2 := rayFlatScaleVec_sq K hc hti v.1
    rw [Pi.inv_apply] at h2
    rw [← mul_inv, ← pow_two, h2, mul_inv, inv_inv, Real.mul_self_sqrt (htw v.1).le]
  have hreal : (∏ v ∈ S, rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹
      * (∏ v ∈ S, rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹
      = ((rayScale K ⊤ 𝔞)⁻¹) ^ S.card
          * ∏ v ∈ S, Real.sqrt (t v.1) * Real.sqrt (t v.1) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      show (∏ v ∈ S, (rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹
          * (rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹)
        = ∏ v ∈ S, (rayScale K ⊤ 𝔞)⁻¹ * (Real.sqrt (t v.1) * Real.sqrt (t v.1)) from
        Finset.prod_congr rfl fun v _ => hplace v,
      Finset.prod_mul_distrib, Finset.prod_const]
  have hCF2 : ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
      * ((((∏ v ∈ S, rayFlatScaleVec K (rayScale K ⊤ 𝔞) t⁻¹ v.1)⁻¹ : ℝ)) : ℂ)
      = (1 / ((rayScale K ⊤ 𝔞 : ℝ) : ℂ)) ^ S.card
          * (raySWeight K S t * raySWeight K S t) := by
    rw [← Complex.ofReal_mul, hreal, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_inv, raySWeight, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
    rw [show (∏ v ∈ S, ((Real.sqrt (t v.1) * Real.sqrt (t v.1) : ℝ) : ℂ))
        = ∏ v ∈ S, (((Real.sqrt (t (v : InfinitePlace K)) : ℝ) : ℂ)
            * ((Real.sqrt (t (v : InfinitePlace K)) : ℝ) : ℂ)) from
      Finset.prod_congr rfl fun v _ => by push_cast; ring]
    rw [one_div]

  rcases Finset.eq_empty_or_nonempty S with hSe | hSne
  · simp only [hSe, Finset.prod_empty, Finset.card_empty, pow_zero, raySWeight, polyS_realUnit,
      Complex.ofReal_one, inv_one, one_mul, mul_one, if_true]
    ring
  · have hp00 : polyS (realUnit K) S 0 = 0 := by
      obtain ⟨v, hv⟩ := hSne
      rw [polyS_realUnit]
      exact Finset.prod_eq_zero hv (by simp)
    rw [if_neg (Finset.nonempty_iff_ne_empty.mp hSne)]
    simp only [hp00, mul_zero, zero_mul, zero_add, add_zero, sub_zero, neg_zero]
    have hSW0 : raySWeight K S t ≠ 0 := by
      rw [raySWeight]
      exact Finset.prod_ne_zero_iff.mpr fun v _ =>
        Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (htw v.1))
    have hSWc : (raySWeight K S t)⁻¹ * raySWeight K S t = 1 := inv_mul_cancel₀ hSW0
    linear_combination (uWeight K ⊤ χ S 𝔞 x₀ * (-Complex.I) ^ S.card
        * ((((ZLattice.covolume (dilRayLattice K ⊤ 𝔞 top_ne_bot) volume : ℝ)) : ℂ))⁻¹
        * ((((Real.sqrt (rayScale K ⊤ 𝔞 ^ Module.finrank ℚ K) : ℝ)) : ℂ))⁻¹
        * (((torusNorm K t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ)
            * ((torusNorm K t : ℝ) : ℂ) ^ (-(s / 2)))
        * (raySWeight K S t)⁻¹
        * ∑' z : {z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
            (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
              * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
                  * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ)) * hCF2
      + (uWeight K ⊤ χ S 𝔞 x₀ * (-Complex.I) ^ S.card
        * ((((ZLattice.covolume (dilRayLattice K ⊤ 𝔞 top_ne_bot) volume : ℝ)) : ℂ))⁻¹
        * ((((Real.sqrt (rayScale K ⊤ 𝔞 ^ Module.finrank ℚ K) : ℝ)) : ℂ))⁻¹
        * (((torusNorm K t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ)
            * ((torusNorm K t : ℝ) : ℂ) ^ (-(s / 2)))
        * (1 / ((rayScale K ⊤ 𝔞 : ℝ) : ℂ)) ^ S.card * raySWeight K S t
        * ∑' z : {z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
            (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
              * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
                  * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ)) * hSWc

private theorem tc2CancelTop {ι : Type} [Fintype ι]
    (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (_hpar : IsParity K ⊤ χ S)
    (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞 i))
    (x₀ : ι → K)
    (_hx₀ : ∀ i, IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i))
    (hχ : χ ≠ 1) (s : ℂ) :
    (∑ i : ι, tc2Alpha K ⊤ S (𝔞 i) s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i) = 0)
    ∧ (∑ i : ι, tc2Alpha K ⊤ S (𝔞 i) s * topInvPolar0 K χ S (𝔞 i) = 0) := by
  by_cases hS : S = ∅
  · subst hS

    have hbij' : Function.Bijective fun i => (ClassGroup.mk K (𝔞 i))⁻¹ :=
      (Function.bijective_iff_existsUnique _).mpr fun C =>
        (hbij.existsUnique C⁻¹).imp fun i ⟨hi, hu⟩ =>
          ⟨inv_eq_iff_eq_inv.mpr hi, fun j hj => hu j (inv_eq_iff_eq_inv.mp hj)⟩
    have hsum0 : ∑ i : ι, topWideChar K χ _hpar (ClassGroup.mk K (𝔞 i))⁻¹ = 0 := by
      rw [Fintype.sum_bijective _ hbij' _ (topWideChar K χ _hpar ·) (fun _ => rfl)]
      exact sum_hom_units_eq_zero (topWideChar K χ _hpar) (topWideChar_ne_one K χ _hpar hχ)
    refine ⟨?_, ?_⟩
    ·

      have hfac : ((Real.sqrt (Ideal.absNorm (⊤ : Ideal (𝓞 K)) : ℝ) : ℝ) : ℂ)⁻¹ = 1 := by
        rw [Ideal.absNorm_top, Nat.cast_one, Real.sqrt_one, ofReal_one, inv_one]
      have hx0 : ∀ i, (x₀ i : K) ≠ 0 := fun i h => (_hx₀ i).2 (by
        rw [h, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero])
      simp only [rayInvPolarCoeff_eq K ⊤ χ ∅ (𝔞 _) top_ne_bot (x₀ _) rfl, hfac, mul_one,
        uWeight_top_eq_topWideChar_inv K χ _hpar (𝔞 _) (hx0 _),
        tc2Alpha, Finset.card_empty, pow_zero, mul_one, ← Finset.mul_sum, hsum0, mul_zero]
    ·
      simp only [topInvPolar0, ite_true, tc2Alpha, Finset.card_empty, pow_zero, mul_one,
        uWeight_top_eq_topWideChar_inv K χ _hpar (𝔞 _) one_ne_zero]
      rw [show (∑ i : ι, tc2Const K * -topWideChar K χ _hpar (ClassGroup.mk K (𝔞 i))⁻¹)
          = -tc2Const K * ∑ i : ι, topWideChar K χ _hpar (ClassGroup.mk K (𝔞 i))⁻¹ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        hsum0, mul_zero]
  ·
    refine ⟨Finset.sum_eq_zero fun i _ => ?_, Finset.sum_eq_zero fun i _ => ?_⟩
    · rw [rayInvPolarCoeff_eq_zero_of_ne_empty K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i) hS, mul_zero]
    · rw [topInvPolar0, if_neg hS, neg_zero, mul_zero]

end TopSlice
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end M4aTorus
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end TcFold_M4aTorus_RayTc2
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section TcFold_SKELETON

set_option autoImplicit false

noncomputable section

namespace M4aTorus
p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
namespace WallSol
p2m_open "M4aTorus"

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
p2m_open "MeasureTheory Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
open scoped nonZeroDivisors Classical Real

section Glue

private def U01 : Set ℂ := {s : ℂ | s ≠ 0 ∧ s ≠ 1}

private theorem U01_eq_compl : U01 = ({0, 1} : Set ℂ)ᶜ := by
  ext s
  simp [U01, not_or]

private theorem isOpen_U01 : IsOpen U01 := by
  rw [U01_eq_compl]
  exact ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl

private theorem isPreconnected_U01 : IsPreconnected U01 := by
  rw [U01_eq_compl]
  exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    ((Set.finite_singleton (1 : ℂ)).insert 0).countable).isPreconnected

private theorem ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 := by
  rintro rfl
  norm_num at hs

private theorem mem_U01_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ∈ U01 := by
  refine ⟨ne_zero_of_one_lt_re hs, ?_⟩
  rintro rfl
  norm_num at hs

private theorem one_sub_mem_U01 {s : ℂ} (hs : s ∈ U01) : 1 - s ∈ U01 :=
  ⟨fun h => hs.2 (sub_eq_zero.mp h).symm, fun h => hs.1 (sub_eq_self.mp h)⟩

private theorem differentiableOn_comp_one_sub {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U01) :
    DifferentiableOn ℂ (fun s => F (1 - s)) U01 :=
  hF.comp ((differentiable_const (1 : ℂ)).sub differentiable_id).differentiableOn
    fun _ hs => one_sub_mem_U01 hs

private theorem eqOn_U01_of_eqOn_right {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U01)
    (hg : DifferentiableOn ℂ g U01) (h : ∀ s : ℂ, 1 < s.re → f s = g s) :
    ∀ s ∈ U01, f s = g s := by
  have h2 : (2 : ℂ) ∈ U01 := mem_U01_of_one_lt_re (by norm_num)
  have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : f =ᶠ[nhds (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (ho.mem_nhds (by norm_num)) fun s hs => h s hs
  exact (hf.analyticOnNhd isOpen_U01).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd isOpen_U01) isPreconnected_U01 h2 hev

variable {ι : Type} [Fintype ι]

private def perIdeal (High ID q₁ q₀ : ℂ → ℂ) (P₁ P₀ : ℂ) (s : ℂ) : ℂ :=
  High s + ID s + P₁ * q₁ s + P₀ * q₀ s

private theorem differentiableOn_perIdeal {High ID q₁ q₀ : ℂ → ℂ} {P₁ P₀ : ℂ}
    (hH : Differentiable ℂ High) (hI : Differentiable ℂ ID)
    (hq₁ : DifferentiableOn ℂ q₁ U01) (hq₀ : DifferentiableOn ℂ q₀ U01) :
    DifferentiableOn ℂ (perIdeal High ID q₁ q₀ P₁ P₀) U01 := by
  unfold perIdeal
  exact ((hH.differentiableOn.add hI.differentiableOn).add
    ((differentiableOn_const _).mul hq₁)).add ((differentiableOn_const _).mul hq₀)

private theorem perIdeal_eq_of_split {High ID q₁ q₀ m : ℂ → ℂ} {P₁ P₀ : ℂ} {pol₁ pol₀ : ℂ → ℂ}
    (hsplit : ∀ s : ℂ, 1 < s.re → m s = High s + ID s + P₁ * pol₁ s + P₀ * pol₀ s)
    (hq₁ : ∀ s : ℂ, 1 < s.re → pol₁ s = q₁ s) (hq₀ : ∀ s : ℂ, 1 < s.re → pol₀ s = q₀ s)
    {s : ℂ} (hs : 1 < s.re) : perIdeal High ID q₁ q₀ P₁ P₀ s = m s := by
  rw [perIdeal, hsplit s hs, hq₁ s hs, hq₀ s hs]

private theorem differentiableOn_sum_mul (α M : ι → ℂ → ℂ) (hα : ∀ i, Differentiable ℂ (α i))
    (hM : ∀ i, DifferentiableOn ℂ (M i) U01) :
    DifferentiableOn ℂ (fun s => ∑ i, α i s * M i s) U01 :=
  DifferentiableOn.fun_sum fun i _ => (hα i).differentiableOn.mul (hM i)

private theorem sum_mul_eq_of_eq (α M m : ι → ℂ → ℂ) (Λ : ℂ → ℂ)
    (hmM : ∀ i, ∀ s : ℂ, 1 < s.re → M i s = m i s)
    (hΛ : ∀ s : ℂ, 1 < s.re → Λ s = ∑ i, α i s * m i s) {s : ℂ} (hs : 1 < s.re) :
    (∑ i, α i s * M i s) = Λ s := by
  rw [hΛ s hs]
  exact Finset.sum_congr rfl fun i _ => by rw [hmM i s hs]

private theorem sum_mul_perIdeal_eq (α High ID : ι → ℂ → ℂ) (q₁ q₀ : ℂ → ℂ) (P₁ P₀ : ι → ℂ)
    (s : ℂ) :
    (∑ i, α i s * perIdeal (High i) (ID i) q₁ q₀ (P₁ i) (P₀ i) s)
      = (∑ i, α i s * (High i s + ID i s))
          + (∑ i, α i s * P₁ i) * q₁ s + (∑ i, α i s * P₀ i) * q₀ s := by
  simp only [perIdeal, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem differentiable_sum_mul_perIdeal_of_cancel (α High ID : ι → ℂ → ℂ) (q₁ q₀ : ℂ → ℂ)
    (P₁ P₀ : ι → ℂ) (hα : ∀ i, Differentiable ℂ (α i)) (hH : ∀ i, Differentiable ℂ (High i))
    (hI : ∀ i, Differentiable ℂ (ID i))
    (hcancel : ∀ s : ℂ, (∑ i, α i s * P₁ i) = 0 ∧ (∑ i, α i s * P₀ i) = 0) :
    Differentiable ℂ (fun s => ∑ i, α i s * perIdeal (High i) (ID i) q₁ q₀ (P₁ i) (P₀ i) s) := by
  have hfun : (fun s => ∑ i, α i s * perIdeal (High i) (ID i) q₁ q₀ (P₁ i) (P₀ i) s)
      = fun s => ∑ i, α i s * (High i s + ID i s) := by
    funext s
    rw [sum_mul_perIdeal_eq, (hcancel s).1, (hcancel s).2]
    ring
  rw [hfun]
  exact Differentiable.fun_sum fun i _ => (hα i).mul ((hH i).add (hI i))

private theorem fe_right_of_legs (αF HighF IDF HighG mG : ι → ℂ → ℂ) (ΛG : ℂ → ℂ) (ε : ℂ)
    (hID : ∀ i, ∀ s : ℂ, IDF i (1 - s) = ε * HighG i s)
    (hrev : ∀ i, ∀ s : ℂ, 1 < s.re → ε * mG i s = ε * HighG i s + HighF i (1 - s))
    (hT : ∀ s : ℂ, 1 < s.re → ΛG s = ∑ i, αF i (1 - s) * mG i s)
    {s : ℂ} (hs : 1 < s.re) :
    (∑ i, αF i (1 - s) * (HighF i (1 - s) + IDF i (1 - s))) = ε * ΛG s := by
  rw [hT s hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hID i s, ← mul_assoc ε, mul_comm ε (αF i (1 - s)), mul_assoc, hrev i s hs]
  ring

end Glue
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section Bot

variable (K : Type) [Field K] [NumberField K]

private theorem completedRayL_bot (χ : NarrowRayClassGroup K ⊥ →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) {s : ℂ} (hs : s ≠ 0) :
    completedRayL K ⊥ χ S s = 0 := by
  have h : ((|(discr K : ℝ)| * (Ideal.absNorm (⊥ : Ideal (𝓞 K)) : ℝ) : ℝ) : ℂ) ^ (s / 2) = 0 := by
    rw [Ideal.absNorm_bot, Nat.cast_zero, mul_zero, Complex.ofReal_zero,
      Complex.zero_cpow (div_ne_zero hs two_ne_zero)]
  rw [completedRayL, h]
  simp

end Bot
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section Holes

variable (K : Type) [Field K] [NumberField K]
variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
variable (S : Finset {w : InfinitePlace K // IsReal w})
variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

private theorem uWeight_zero : uWeight K 𝔣 χ S 𝔞 0 = 0 := by
  rw [uWeight, FractionalIdeal.spanSingleton_zero, zero_mul, chiIdeal_zero, zero_mul]

private theorem norm_uWeight_mul_prod_le (h𝔣 : 𝔣 ≠ ⊥) (y : K) :
    ‖uWeight K 𝔣 χ S 𝔞 y * ∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ)‖
      ≤ 1 * ∏ v ∈ S, (v.1 : InfinitePlace K) y := by
  rw [norm_mul, norm_prod]
  refine mul_le_mul (norm_uWeight_le_one K 𝔣 χ S 𝔞 h𝔣 y)
    (le_of_eq (Finset.prod_congr rfl fun v _ => ?_)) (by positivity) zero_le_one
  rw [Complex.norm_real, norm_embedding_of_isReal]

private theorem norm_addChar (x : K) : ‖addChar K x‖ = 1 := by
  rw [addChar]
  have : (2 * π * Complex.I * (Algebra.trace ℚ K x : ℂ))
      = ((2 * π * (Algebra.trace ℚ K x : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private theorem norm_chiFin_le_one (h𝔣 : 𝔣 ≠ ⊥) (α : 𝓞 K) : ‖chiFin K 𝔣 χ S α‖ ≤ 1 := by
  rw [chiFin, norm_mul]
  rcases eq_or_ne α 0 with rfl | hα
  · have h0 : ((Ideal.span {(0 : 𝓞 K)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      rw [Ideal.span_singleton_eq_bot.mpr rfl, FractionalIdeal.coeIdeal_bot]
    rw [h0, chiIdeal_zero, norm_zero, zero_mul]
    exact zero_le_one
  · have hI : ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
      exact hα
    have hα' : (α : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hα
    have hsign : ‖signAt K S (α : K)‖ = 1 := by
      have h := normSq_signAt S hα'
      rw [Complex.normSq_eq_norm_sq] at h
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (h.trans (one_pow 2).symm)
    rw [hsign, mul_one]
    by_cases hIc : Units.mk0 _ hI ∈ coprimeToModulus K 𝔣
    · exact (norm_chiIdeal_of_mem χ h𝔣 hI hIc).le
    · rw [chiIdeal_eq_zero_of_not_mem χ hI hIc, norm_zero]
      exact zero_le_one

private theorem norm_gaussCore_le (h𝔣 : 𝔣 ≠ ⊥) (y : K) :
    ‖gaussCore χ h𝔣 S y‖ ≤ Nat.card (𝓞 K ⧸ 𝔣) := by
  haveI : Finite (𝓞 K ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  unfold gaussCore
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun r _ => ?_).trans ?_
  · rw [norm_mul, norm_addChar, mul_one]
    exact norm_chiFin_le_one K 𝔣 χ S h𝔣 _
  · rw [nsmul_eq_mul, mul_one]
    exact_mod_cast (Nat.card_eq_finsetCard _).symm.trans_le
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

private theorem norm_gaussCore_mul_prod_le (h𝔣 : 𝔣 ≠ ⊥) (x₀ y : K) :
    ‖gaussCore χ h𝔣 S (x₀ * y) * ∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ)‖
      ≤ (Nat.card (𝓞 K ⧸ 𝔣) : ℝ) * ∏ v ∈ S, (v.1 : InfinitePlace K) y := by
  rw [norm_mul, norm_prod]
  refine mul_le_mul (norm_gaussCore_le K 𝔣 χ S h𝔣 _)
    (le_of_eq (Finset.prod_congr rfl fun v _ => ?_)) (by positivity) (by positivity)
  rw [Complex.norm_real, norm_embedding_of_isReal]

private scoped instance instCountableFracIdeal (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Countable ↥(𝔟 : FractionalIdeal (𝓞 K)⁰ K) :=
  Countable.of_equiv _ (M4aP2.idealPointEquiv K 𝔟).symm

private theorem tsum_rayFoldSummand_eq_tsum_ne_zero (c : ℝ) (t : realSpace K) :
    (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
      = ∑' y : {y : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (y : K) ≠ 0},
          rayFoldSummand K 𝔣 χ S 𝔞 c t (y.1 : K) := by
  refine (tsum_subtype_eq_of_support_subset
    (f := fun x : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) => rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
    (s := {y : ↥(𝔞 : FractionalIdeal (𝓞 K)⁰ K) | (y : K) ≠ 0}) ?_).symm
  intro y hy h0
  apply hy
  show rayFoldSummand K 𝔣 χ S 𝔞 c t (y : K) = 0
  rw [h0, rayFoldSummand, uWeight_zero, zero_mul, zero_mul]

private theorem exists_tail_bound_rayTheta (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t},
      ‖(∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
          * raySWeight K S t‖
        ≤ C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨C, γ, hγ, h⟩ := tail_bound_highHalf K 𝔞 hc S
    (fun y => uWeight K 𝔣 χ S 𝔞 y * ∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ)) zero_le_one
    (fun y => norm_uWeight_mul_prod_le K 𝔣 χ S 𝔞 h𝔣 y)
  refine ⟨C, γ, hγ, fun t ht => ?_⟩
  rw [tsum_rayFoldSummand_eq_tsum_ne_zero, norm_mul]
  simpa only [rayFoldSummand, raySWeight] using h t ht

private theorem exists_tail_bound_dualTheta (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t},
      ‖(∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          gaussCore χ h𝔣 S (x₀ * (z.1 : K))
            * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
          * raySWeight K S t‖
        ≤ C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  have hc : 0 < 1 / rayScale K 𝔣 𝔞 := by
    have := rayScale_pos K 𝔣 h𝔣 𝔞
    positivity
  obtain ⟨C, γ, hγ, h⟩ := tail_bound_highHalf K (rayDualIdeal K 𝔣 h𝔣 𝔞) hc S
    (fun y => gaussCore χ h𝔣 S (x₀ * y) * ∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ))
    (Nat.cast_nonneg _) (fun y => norm_gaussCore_mul_prod_le K 𝔣 χ S h𝔣 x₀ y)
  refine ⟨C, γ, hγ, fun t ht => ?_⟩
  rw [norm_mul]
  simpa only [raySWeight] using h t ht

private theorem measurable_rayThetaW (c : ℝ) :
    Measurable fun t : realSpace K =>
      (∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
        * raySWeight K S t := by
  refine Measurable.mul (Measurable.tsum fun x => ?_) ?_
  · unfold rayFoldSummand
    exact (measurable_const.mul measurable_const).mul (Complex.measurable_ofReal.comp
      ((measurable_torusForm_left K (mixedEmbedding K (x : K))).const_mul (-Real.pi * c)).exp)
  · unfold raySWeight
    exact Finset.measurable_prod S fun v _ => Complex.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp (measurable_pi_apply _))

private theorem measurable_dualThetaW (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) :
    Measurable fun t : realSpace K =>
      (∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          gaussCore χ h𝔣 S (x₀ * (z.1 : K))
            * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
        * raySWeight K S t := by
  refine Measurable.mul (Measurable.tsum fun z => ?_) ?_
  · exact (measurable_const.mul measurable_const).mul (Complex.measurable_ofReal.comp
      ((measurable_torusForm_left K (mixedEmbedding K (z.1 : K))).const_mul _).exp)
  · unfold raySWeight
    exact Finset.measurable_prod S fun v _ => Complex.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp (measurable_pi_apply _))

omit [NumberField K] in

private theorem norm_prod_embedding_le (y : K) :
    ‖∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ)‖ ≤ (1 : ℝ) * ∏ v ∈ S, (v.1 : InfinitePlace K) y := by
  rw [one_mul, norm_prod]
  exact le_of_eq (Finset.prod_congr rfl fun v _ => by rw [Complex.norm_real, norm_embedding_of_isReal])

private theorem exists_tail_bound_dualTheta₁ (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t},
      ‖(∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
          * raySWeight K S t‖
        ≤ C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  have hc : 0 < 1 / rayScale K 𝔣 𝔞 := by
    have := rayScale_pos K 𝔣 h𝔣 𝔞
    positivity
  obtain ⟨C, γ, hγ, h⟩ := tail_bound_highHalf K (rayDualIdeal K 𝔣 h𝔣 𝔞) hc S
    (fun y => ∏ v ∈ S, ((embedding_of_isReal v.2 y : ℝ) : ℂ))
    zero_le_one (fun y => norm_prod_embedding_le K S y)
  refine ⟨C, γ, hγ, fun t ht => ?_⟩
  rw [norm_mul]
  simpa only [raySWeight] using h t ht

private theorem measurable_dualThetaW₁ (h𝔣 : 𝔣 ≠ ⊥) :
    Measurable fun t : realSpace K =>
      (∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
          (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
            * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
                * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
        * raySWeight K S t := by
  refine Measurable.mul (Measurable.tsum fun z => ?_) ?_
  · exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_torusForm_left K (mixedEmbedding K (z.1 : K))).const_mul _).exp)
  · unfold raySWeight
    exact Finset.measurable_prod S fun v _ => Complex.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp (measurable_pi_apply _))

private theorem hole_high_integrable (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c) (s : ℂ) :
    IntegrableOn (rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := by
  obtain ⟨C, γ, hγ, h⟩ := exists_tail_bound_rayTheta K 𝔣 χ S 𝔞 h𝔣 hc
  have hmeas : Measurable (rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s) := by
    have h1 := measurable_rayThetaW K 𝔣 χ S 𝔞 c
    have h2 : Measurable fun t : realSpace K => ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) :=
      (Complex.measurable_ofReal.comp (measurable_torusNorm K)).pow_const _
    have hfun : rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s = fun t =>
        ((∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
          * raySWeight K S t) * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) := by
      funext t
      simp only [rayFoldMellinIntegrand, rayMellinWeight]
      ring
    rw [hfun]
    exact h1.mul h2
  refine integrableOn_highHalf_of_norm_le K hmeas.aestronglyMeasurable C hγ (s.re / 2)
    fun t ht => ?_
  have hN0 := torusNorm_pos_of_mem_highHalf K ht
  have hre : ‖((torusNorm K t : ℝ) : ℂ) ^ (s / 2)‖ = torusNorm K t ^ (s.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0, Complex.div_ofNat_re]
  calc ‖rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t‖
      = ‖(∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
          * raySWeight K S t‖ * torusNorm K t ^ (s.re / 2) := by
        rw [rayFoldMellinIntegrand, rayMellinWeight, ← hre, ← norm_mul]
        congr 1
        ring
    _ ≤ C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
          * torusNorm K t ^ (s.re / 2) :=
        mul_le_mul_of_nonneg_right (h t ht) (Real.rpow_nonneg hN0.le _)

private theorem hole_high_differentiable (h𝔣 : 𝔣 ≠ ⊥) {c : ℝ} (hc : 0 < c) :
    Differentiable ℂ fun s => rayFoldMellinHigh K 𝔣 χ S 𝔞 c s := by
  obtain ⟨C, γ, hγ, h⟩ := exists_tail_bound_rayTheta K 𝔣 χ S 𝔞 h𝔣 hc
  have hD := differentiable_setIntegral_highHalf_mul_cpow K (measurable_rayThetaW K 𝔣 χ S 𝔞 c)
    C hγ 0 (fun t ht => by simpa using h t ht)
  have hfun : (fun s => rayFoldMellinHigh K 𝔣 χ S 𝔞 c s)
      = fun s => ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
          ((∑' x : (𝔞 : FractionalIdeal (𝓞 K)⁰ K), rayFoldSummand K 𝔣 χ S 𝔞 c t (x : K))
            * raySWeight K S t) * ((torusNorm K t : ℝ) : ℂ) ^ (s / 2) ∂(torusHaar K) := by
    funext s
    refine setIntegral_congr_fun (measurableSet_highHalf K) fun t _ => ?_
    simp only [rayFoldMellinIntegrand, rayMellinWeight]
    ring
  rw [hfun]
  exact hD

private def dualThetaW (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (t : realSpace K) : ℂ :=
  (∑' z : {z : ↥(rayDualIdeal K 𝔣 h𝔣 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
      gaussCore χ h𝔣 S (x₀ * (z.1 : K))
        * (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
        * ((Real.exp (-π * (1 / rayScale K 𝔣 𝔞)
            * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
    * raySWeight K S t

private theorem rayInvDual_eq (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (s : ℂ) (t : realSpace K) :
    rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ s t
      = rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀
          * (dualThetaW K 𝔣 χ S 𝔞 h𝔣 x₀ t * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)) := by
  simp only [rayInvDual, dualThetaW, rayMellinWeight]
  ring

private theorem hole_dual_integrable (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (s : ℂ) :
    IntegrableOn (rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ s)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := by
  obtain ⟨C, γ, hγ, h⟩ := exists_tail_bound_dualTheta K 𝔣 χ S 𝔞 h𝔣 x₀
  have h1 : Measurable (dualThetaW K 𝔣 χ S 𝔞 h𝔣 x₀) := measurable_dualThetaW K 𝔣 χ S 𝔞 h𝔣 x₀
  have h2 : Measurable fun t : realSpace K => ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2) :=
    (Complex.measurable_ofReal.comp (measurable_torusNorm K)).pow_const _
  have hfun : rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ s = fun t => rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀
      * (dualThetaW K 𝔣 χ S 𝔞 h𝔣 x₀ t * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)) :=
    funext (rayInvDual_eq K 𝔣 χ S 𝔞 h𝔣 x₀ s)
  have hmeas : Measurable (rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ s) := by
    rw [hfun]
    exact (h1.mul h2).const_mul _
  refine integrableOn_highHalf_of_norm_le K hmeas.aestronglyMeasurable
    (‖rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀‖ * C) hγ ((1 - s).re / 2) fun t ht => ?_
  have hN0 := torusNorm_pos_of_mem_highHalf K ht
  rw [rayInvDual_eq, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN0,
    Complex.div_ofNat_re]
  have hb := h t ht
  rw [← dualThetaW] at hb
  calc ‖rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀‖
        * (‖dualThetaW K 𝔣 χ S 𝔞 h𝔣 x₀ t‖ * torusNorm K t ^ ((1 - s).re / 2))
      ≤ ‖rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀‖
        * (C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
          * torusNorm K t ^ ((1 - s).re / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hN0.le _))
          (norm_nonneg _)
    _ = _ := by ring

private theorem hole_dual_differentiable (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) :
    Differentiable ℂ fun s =>
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ s t
        ∂(torusHaar K) := by
  obtain ⟨C, γ, hγ, h⟩ := exists_tail_bound_dualTheta K 𝔣 χ S 𝔞 h𝔣 x₀
  have hD := differentiable_setIntegral_highHalf_mul_cpow K
    (measurable_dualThetaW K 𝔣 χ S 𝔞 h𝔣 x₀) C hγ 0 (fun t ht => by simpa using h t ht)
  have hfun : (fun s => ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
        rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ s t ∂(torusHaar K))
      = fun s => rayInvConst K 𝔣 χ S 𝔞 h𝔣 x₀
          * ((fun s' : ℂ => ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
              dualThetaW K 𝔣 χ S 𝔞 h𝔣 x₀ t * ((torusNorm K t : ℝ) : ℂ) ^ (s' / 2)
                ∂(torusHaar K)) (1 - s)) := by
    funext s
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_highHalf K) fun t _ =>
      rayInvDual_eq K 𝔣 χ S 𝔞 h𝔣 x₀ s t
  rw [hfun]
  exact (hD.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul _

private theorem hole_polar_integrable {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun t => ((torusNorm K t : ℝ) : ℂ) ^ z)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) :=
  integrableOn_highHalf_torusNorm_cpow_of_re_neg K hz

private theorem hole_polar_eval :
    ∃ V : ℂ, ∀ {z : ℂ}, 0 < z.re →
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z)
        ∂(torusHaar K) = V / z :=
  ⟨polarVolume K, fun hz => setIntegral_highHalf_torusNorm_cpow_neg K hz⟩
end Holes
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

section Assembly

variable (K : Type) [Field K] [NumberField K]

private def WallConj (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (F G : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
  DifferentiableOn ℂ G {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
  (∀ s : ℂ, 1 < s.re → F s = completedRayL K 𝔣 χ S s) ∧
  (∀ s : ℂ, 1 < s.re →
    G s = completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
  (∀ h𝔣 : 𝔣 ≠ ⊥, ∀ _ : 𝔣 ≠ ⊤, ∀ y₀ : K, M4aP2.IsGaussDatum K 𝔣 χ y₀ →
    M4aP2.IsPrimitiveMod K 𝔣 χ →
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      F (1 - s) = (-Complex.I) ^ S.card *
        (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) * G s) ∧
  (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G)

private theorem isParity_conj {𝔣 : Ideal (𝓞 K)} {χ : NarrowRayClassGroup K 𝔣 →* ℂ}
    {S : Finset {w : InfinitePlace K // IsReal w}} (hS : IsParity K 𝔣 χ S) :
    IsParity K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S := by
  intro α hα h1
  have h := chiIdeal_conjChar 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
  rw [hS α hα h1] at h
  refine h.trans ?_
  unfold signAt
  rw [map_prod]
  exact Finset.prod_congr rfl fun v _ => map_intCast (starRingEnd ℂ) _

private theorem conjChar_ne_one {𝔣 : Ideal (𝓞 K)} {χ : NarrowRayClassGroup K 𝔣 →* ℂ} (hχ : χ ≠ 1) :
    (starRingEnd ℂ).toMonoidHom.comp χ ≠ 1 := by
  intro h
  apply hχ
  refine MonoidHom.ext fun C => ?_
  have hC : (starRingEnd ℂ) (χ C) = 1 := DFunLike.congr_fun h C
  have h2 := congrArg (starRingEnd ℂ) hC
  simpa using h2

private theorem exists_chiFin_ne_of_isPrimitiveMod {𝔣 : Ideal (𝓞 K)} {χ : NarrowRayClassGroup K 𝔣 →* ℂ}
    (S : Finset {w : InfinitePlace K // IsReal w}) (h𝔣' : 𝔣 ≠ ⊤) (hprim : IsPrimitiveMod K 𝔣 χ) :
    ∃ α : 𝓞 K, chiFin K 𝔣 χ S α ≠ 0 ∧ chiFin K 𝔣 χ S α ≠ 1 := by
  obtain ⟨α, -, -, hpos, h0, h1⟩ := hprim ⊤ le_top (Ne.symm h𝔣')
  have hsign : signAt K S (α : K) = 1 := by
    unfold signAt
    refine Finset.prod_eq_one fun v _ => ?_
    rw [sign_pos (hpos _), SignType.coe_one, Int.cast_one]
  refine ⟨α, ?_, ?_⟩
  · rw [chiFin, hsign, mul_one]
    exact h0
  · rw [chiFin, hsign, mul_one]
    exact h1

private def qOne (V s : ℂ) : ℂ := V / ((s - 1) / 2)

private theorem differentiableOn_qOne (V : ℂ) : DifferentiableOn ℂ (qOne V) U01 := by
  show DifferentiableOn ℂ (fun s => V / ((s - 1) / 2)) U01
  refine DifferentiableOn.div (differentiableOn_const V)
    ((differentiable_id.sub_const (1 : ℂ)).div_const (2 : ℂ)).differentiableOn ?_
  intro s hs h
  rcases div_eq_zero_iff.mp h with h1 | h2
  · exact hs.2 (sub_eq_zero.mp h1)
  · exact two_ne_zero h2

section MainBranch

variable {K}
variable {𝔣 : Ideal (𝓞 K)}

private theorem mul_rayFoldMellin_split_of_inv (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w})
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℝ) (s : ℂ) (e : ℂ)
    (D : realSpace K → ℂ) (P : ℂ) (pol : realSpace K → ℂ)
    (hInt : IntegrableOn (rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s)
      (foldDomain K) (torusHaar K))
    (hIntD : IntegrableOn D (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K))
    (hIntP : IntegrableOn pol (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K))
    (hinv : ∀ t ∈ orthant K, e * rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t⁻¹
        = D t + P * pol t) :
    e * rayFoldMellin K 𝔣 χ S 𝔞 c s
      = e * rayFoldMellinHigh K 𝔣 χ S 𝔞 c s
        + (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, D t ∂(torusHaar K))
        + P * (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, pol t ∂(torusHaar K)) := by
  have hN1 := measurableSet_torusNorm_ge_one K
  have hN1' : MeasurableSet {t : realSpace K | 1 ≤ torusNorm K t⁻¹} :=
    hN1.preimage (measurable_inv_realSpace K)
  have hHigh : MeasurableSet (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}) :=
    (measurableSet_foldDomain K).inter hN1
  have hIntPP : IntegrableOn (fun t => P * pol t)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := hIntP.const_mul P
  have key : e * (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
        rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t⁻¹ ∂(torusHaar K))
      = (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, D t ∂(torusHaar K))
        + P * (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, pol t ∂(torusHaar K)) :=
    calc e * (∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
            rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t⁻¹ ∂(torusHaar K))
        = ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
            e * rayFoldMellinIntegrand K 𝔣 χ S 𝔞 c s t⁻¹ ∂(torusHaar K) :=
          (integral_const_mul e _).symm
      _ = ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, (D t + P * pol t) ∂(torusHaar K) :=
          setIntegral_congr_fun hHigh fun t ht => hinv t (foldDomain_subset_orthant K ht.1)
      _ = _ := by rw [integral_add hIntD hIntPP, integral_const_mul]
  unfold rayFoldMellin rayFoldMellinHigh
  conv_lhs => rw [foldDomain_eq_union_halves K]
  rw [setIntegral_union₀ (aedisjoint_foldDomainHighHalves K)
      ((measurableSet_foldDomain K).inter hN1').nullMeasurableSet
      (hInt.mono_set Set.inter_subset_left) (hInt.mono_set Set.inter_subset_left),
    setIntegral_foldDomainLowHalf_eq_highHalf_comp_inv K
      (rayFoldMellinIntegrand_unitInvariant K 𝔣 χ S 𝔞 c s),
    mul_add, key]
  ring

variable (K 𝔣)
variable (ψ : NarrowRayClassGroup K 𝔣 →* ℂ) (S : Finset {w : InfinitePlace K // IsReal w})

private def highP (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  rayFoldMellinHigh K 𝔣 ψ S 𝔞 (rayScale K 𝔣 𝔞) s

private def dualP (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (s : ℂ) : ℂ :=
  ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, rayInvDual K 𝔣 ψ S 𝔞 h𝔣 x₀ s t ∂(torusHaar K)

private def polP [Fintype (𝓞 K ⧸ 𝔣)] (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) : ℂ :=
  (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 ψ S (Quotient.out a)) * rayInvPolarCoeff K 𝔣 ψ S 𝔞 h𝔣 x₀

private def contP [Fintype (𝓞 K ⧸ 𝔣)] (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔣 : 𝔣 ≠ ⊥) (x₀ : K) (V : ℂ) :
    ℂ → ℂ :=
  perIdeal (highP K 𝔣 ψ S 𝔞) (dualP K 𝔣 ψ S 𝔞 h𝔣 x₀) (qOne V) (qOne V) (polP K 𝔣 ψ S 𝔞 h𝔣 x₀) 0

private theorem differentiableOn_contP [Fintype (𝓞 K ⧸ 𝔣)] (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔣 : 𝔣 ≠ ⊥)
    (x₀ : K) (V : ℂ) : DifferentiableOn ℂ (contP K 𝔣 ψ S 𝔞 h𝔣 x₀ V) U01 :=
  differentiableOn_perIdeal (hole_high_differentiable K 𝔣 ψ S 𝔞 h𝔣 (rayScale_pos K 𝔣 h𝔣 𝔞))
    (hole_dual_differentiable K 𝔣 ψ S 𝔞 h𝔣 x₀) (differentiableOn_qOne V) (differentiableOn_qOne V)

private theorem contP_eq [Fintype (𝓞 K ⧸ 𝔣)] (hS : IsParity K 𝔣 ψ S) (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
    {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 ψ 𝔞 x₀) {V : ℂ}
    (hV : ∀ z : ℂ, 0 < z.re →
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z)
        ∂(torusHaar K) = V / z)
    {s : ℂ} (hs : 1 < s.re) :
    contP K 𝔣 ψ S 𝔞 h𝔣 x₀ V s = rayFoldMellin K 𝔣 ψ S 𝔞 (rayScale K 𝔣 𝔞) s := by
  have hc : 0 < rayScale K 𝔣 𝔞 := rayScale_pos K 𝔣 h𝔣 𝔞
  have hz : ((1 - s) / 2).re < 0 := by
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hz' : 0 < ((s - 1) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hsplit := rayFoldMellin_split_of_inv K 𝔣 ψ S 𝔞 (rayScale K 𝔣 𝔞) s
    (rayInvDual K 𝔣 ψ S 𝔞 h𝔣 x₀ s) (polP K 𝔣 ψ S 𝔞 h𝔣 x₀)
    (fun t => ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2))
    (integrableOn_foldDomain_rayFoldMellinIntegrand K 𝔣 ψ S 𝔞 h𝔣 _ hc hs)
    (hole_dual_integrable K 𝔣 ψ S 𝔞 h𝔣 x₀ s) (hole_polar_integrable K hz)
    (fun t ht => rayFoldMellinIntegrand_inv_gen K 𝔣 ψ S 𝔞 h𝔣 h𝔣' hS hx₀ ht s)
  have hpol : ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
      ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2) ∂(torusHaar K) = qOne V s := by
    have h := hV _ hz'
    rw [show -((s - 1) / 2) = (1 - s) / 2 by ring] at h
    rw [h, qOne]
  rw [contP, perIdeal, hsplit, hpol, zero_mul, add_zero]
  rfl

variable {ψ S}

private theorem wallHalf_of_T2 [Fintype (𝓞 K ⧸ 𝔣)] (hS : IsParity K 𝔣 ψ S) (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
    {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : ι → K)
    (hx₀ : ∀ i, IsCoprimeGenerator K 𝔣 ψ (𝔞 i) (x₀ i)) (α : ι → ℂ → ℂ)
    (hα : ∀ i, Differentiable ℂ (α i)) (Λ : ℂ → ℂ)
    (hT : ∀ s : ℂ, 1 < s.re → Λ s = ∑ i, α i s * rayFoldMellin K 𝔣 ψ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s)
    {V : ℂ} (hV : ∀ z : ℂ, 0 < z.re →
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z)
        ∂(torusHaar K) = V / z) :
    DifferentiableOn ℂ (fun s => ∑ i, α i s * contP K 𝔣 ψ S (𝔞 i) h𝔣 (x₀ i) V s) U01 ∧
    ∀ s : ℂ, 1 < s.re → (∑ i, α i s * contP K 𝔣 ψ S (𝔞 i) h𝔣 (x₀ i) V s) = Λ s :=
  ⟨differentiableOn_sum_mul α _ hα fun i => differentiableOn_contP K 𝔣 ψ S (𝔞 i) h𝔣 (x₀ i) V,
   fun _ hs => sum_mul_eq_of_eq α _ (fun i s => rayFoldMellin K 𝔣 ψ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) Λ
     (fun i _ hs => contP_eq K 𝔣 ψ S hS h𝔣 h𝔣' (hx₀ i) hV hs) hT hs⟩

private theorem rayInvDual_eq_conj [Fintype (𝓞 K ⧸ 𝔣)] {χ : NarrowRayClassGroup K 𝔣 →* ℂ}
    {S : Finset {w : InfinitePlace K // IsReal w}} (hS : IsParity K 𝔣 χ S) (h𝔣 : 𝔣 ≠ ⊥)
    (h𝔣' : 𝔣 ≠ ⊤) (hprim : IsPrimitiveMod K 𝔣 χ) {y : K} (hy : IsGaussDatum K 𝔣 χ y)
    {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x₀ : K} (hx₀ : IsCoprimeGenerator K 𝔣 χ 𝔞 x₀)
    {t : realSpace K} (ht : t ∈ orthant K) (σ : ℂ) :
    rayInvDual K 𝔣 χ S 𝔞 h𝔣 x₀ σ t
      = (-Complex.I) ^ S.card
          * (gaussSumAt K 𝔣 χ h𝔣 S y / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))
          * (1 / ((rayScale K 𝔣 𝔞 : ℝ) : ℂ)) ^ S.card
          * rayFoldMellinIntegrand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
              (rayDualIdeal K 𝔣 h𝔣 𝔞) (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 𝔞)) (1 - σ) t := by
  have h1 := rayFoldMellinIntegrand_inv_gen K 𝔣 χ S 𝔞 h𝔣 h𝔣' hS hx₀ ht σ
  have h2 := rayFoldMellinIntegrand_inv K 𝔣 χ S 𝔞 h𝔣 h𝔣' hS hprim hy hx₀ ht σ
  rw [h1] at h2
  exact add_right_cancel h2

private theorem wallConj_of_T2 [Fintype (𝓞 K ⧸ 𝔣)] (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K 𝔣 χ S)
    (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
    {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x₀ : ι → K) (hx₀ : ∀ i, IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i))
    (x₀' : ι → K) (hx₀' : ∀ i, IsCoprimeGenerator K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ)
      (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (x₀' i))
    (α α' : ι → ℂ → ℂ) (hα : ∀ i, Differentiable ℂ (α i)) (hα' : ∀ i, Differentiable ℂ (α' i))
    (hT : ∀ s : ℂ, 1 < s.re → completedRayL K 𝔣 χ S s
      = ∑ i, α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s)
    (hT' : ∀ s : ℂ, 1 < s.re → completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s
      = ∑ i, α' i s * rayFoldMellin K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
          (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s)
    (hαα' : ∀ i, ∀ s : ℂ, α' i s = α i (1 - s) * (1 / ((rayScale K 𝔣 (𝔞 i) : ℝ) : ℂ)) ^ S.card)
    (hcancel : χ ≠ 1 → ∀ s : ℂ,
      ∑ i, α i s * ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a))
        * rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i)) = 0)
    (hcancel' : χ ≠ 1 → ∀ s : ℂ,
      ∑ i, α' i s * ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (Quotient.out a))
        * rayInvPolarCoeff K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
            (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i)) = 0) :
    ∃ F G : ℂ → ℂ, WallConj K 𝔣 χ S F G := by
  obtain ⟨V, hV⟩ := hole_polar_eval K
  have hV' : ∀ z : ℂ, 0 < z.re →
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z)
        ∂(torusHaar K) = V / z := fun z hz => hV hz
  have hpar' := isParity_conj K hpar

  obtain ⟨hF1, hF3⟩ := wallHalf_of_T2 K 𝔣 hpar h𝔣 h𝔣' 𝔞 x₀ hx₀ α hα
    (fun s => completedRayL K 𝔣 χ S s) hT hV'
  obtain ⟨hG1, hG3⟩ := wallHalf_of_T2 K 𝔣 hpar' h𝔣 h𝔣' (fun i => rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) x₀' hx₀'
    α' hα' (fun s => completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) hT' hV'
  refine ⟨fun s => ∑ i, α i s * contP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) V s,
    fun s => ∑ i, α' i s * contP K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
      (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i) V s, ?_⟩
  unfold WallConj
  refine ⟨hF1, hG1, hF3, hG3, ?_, ?_⟩
  ·
    intro h𝔣₀ h𝔣'₀ y₀ hy hprim s hs0 hs1
    have hne := exists_chiFin_ne_of_isPrimitiveMod K S h𝔣' hprim
    have hsum0 : (∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a)) = 0 :=
      ChiFinOrth.sum_chiFin_out_eq_zero K χ S hpar h𝔣' hne

    have hID : ∀ i, ∀ s : ℂ, dualP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) (1 - s)
        = (-Complex.I) ^ S.card
          * (gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))
          * (1 / ((rayScale K 𝔣 (𝔞 i) : ℝ) : ℂ)) ^ S.card
          * highP K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) s := by
      intro i s
      have hHigh : MeasurableSet (foldDomain K ∩ {t : realSpace K | 1 ≤ torusNorm K t}) :=
        (measurableSet_foldDomain K).inter (measurableSet_torusNorm_ge_one K)
      unfold dualP highP rayFoldMellinHigh
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hHigh fun t ht => ?_
      have h := rayInvDual_eq_conj K 𝔣 hpar h𝔣 h𝔣' hprim hy (hx₀ i)
        (foldDomain_subset_orthant K ht.1) (1 - s)
      rw [sub_sub_cancel] at h
      exact h

    have hrev : ∀ i, ∀ s : ℂ, 1 < s.re →
        (-Complex.I) ^ S.card
            * (gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))
            * (1 / ((rayScale K 𝔣 (𝔞 i) : ℝ) : ℂ)) ^ S.card
            * rayFoldMellin K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))
                (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s
          = (-Complex.I) ^ S.card
              * (gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))
              * (1 / ((rayScale K 𝔣 (𝔞 i) : ℝ) : ℂ)) ^ S.card
              * highP K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) s
            + highP K 𝔣 χ S (𝔞 i) (1 - s) := by
      intro i s hs
      have hc : 0 < rayScale K 𝔣 (𝔞 i) := rayScale_pos K 𝔣 h𝔣 (𝔞 i)
      have hc' : 0 < rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) := rayScale_pos K 𝔣 h𝔣 _
      have h := mul_rayFoldMellin_split_of_inv ((starRingEnd ℂ).toMonoidHom.comp χ) S
        (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s
        ((-Complex.I) ^ S.card
          * (gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))
          * (1 / ((rayScale K 𝔣 (𝔞 i) : ℝ) : ℂ)) ^ S.card)
        (rayFoldMellinIntegrand K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) (1 - s)) 0
        (rayFoldMellinIntegrand K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) (1 - s))
        (integrableOn_foldDomain_rayFoldMellinIntegrand K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
          (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 _ hc' hs)
        (hole_high_integrable K 𝔣 χ S (𝔞 i) h𝔣 hc (1 - s))
        (hole_high_integrable K 𝔣 χ S (𝔞 i) h𝔣 hc (1 - s)) (fun t ht => by
          have ht' : t⁻¹ ∈ orthant K := inv_mem_orthant K ht
          have h1 := rayFoldMellinIntegrand_inv_gen K 𝔣 χ S (𝔞 i) h𝔣 h𝔣' hpar (hx₀ i) ht' (1 - s)
          rw [inv_inv, hsum0, zero_mul, zero_mul, add_zero] at h1
          have h3 := rayInvDual_eq_conj K 𝔣 hpar h𝔣 h𝔣' hprim hy (hx₀ i) ht' (1 - s)
          rw [sub_sub_cancel] at h3
          rw [zero_mul, add_zero, ← h3, ← h1])
      simp only [zero_mul, add_zero] at h
      rw [h]
      rfl

    have hfe : ∀ s : ℂ, 1 < s.re →
        (∑ i, α i (1 - s) * contP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) V (1 - s))
          = (-Complex.I) ^ S.card
              * (gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ))
              * ∑ i, α' i s * contP K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i) V s := by
      intro s hs
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [contP_eq K 𝔣 _ S hpar' h𝔣 h𝔣' (hx₀' i) hV' hs, hαα' i s]
      have hPi : polP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) = 0 := by
        rw [polP, hsum0, zero_mul]
      have hci : contP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) V (1 - s)
          = highP K 𝔣 χ S (𝔞 i) (1 - s) + dualP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i) (1 - s) := by
        simp only [contP, perIdeal, hPi, zero_mul, add_zero]
      rw [hci, hID i s]
      linear_combination (-(α i (1 - s))) * hrev i s hs
    exact eqOn_U01_of_eqOn_right (differentiableOn_comp_one_sub hF1)
      ((differentiableOn_const ((-Complex.I) ^ S.card
        * (gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣 : ℝ) : ℂ)))).mul hG1)
      hfe s ⟨hs0, hs1⟩
  ·
    intro hχ
    refine ⟨?_, ?_⟩
    · exact differentiable_sum_mul_perIdeal_of_cancel α (fun i => highP K 𝔣 χ S (𝔞 i))
        (fun i => dualP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i)) (qOne V) (qOne V)
        (fun i => polP K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i)) (fun _ => 0) hα
        (fun i => hole_high_differentiable K 𝔣 χ S (𝔞 i) h𝔣 (rayScale_pos K 𝔣 h𝔣 (𝔞 i)))
        (fun i => hole_dual_differentiable K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))
        (fun s => ⟨hcancel hχ s, by simp⟩)
    · exact differentiable_sum_mul_perIdeal_of_cancel α'
        (fun i => highP K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)))
        (fun i => dualP K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))
          h𝔣 (x₀' i)) (qOne V) (qOne V)
        (fun i => polP K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))
          h𝔣 (x₀' i)) (fun _ => 0) hα'
        (fun i => hole_high_differentiable K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
          (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (rayScale_pos K 𝔣 h𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))))
        (fun i => hole_dual_differentiable K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
          (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))
        (fun s => ⟨hcancel' hχ s, by simp⟩)

end MainBranch
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

private theorem hole_T2 (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K 𝔣 χ S)
    (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) [Fintype (𝓞 K ⧸ 𝔣)] :
    ∃ (ι : Type) (_ : Fintype ι) (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α α' : ι → ℂ → ℂ),
      (∀ i, Differentiable ℂ (α i)) ∧ (∀ i, Differentiable ℂ (α' i)) ∧
      (∀ s : ℂ, 1 < s.re → completedRayL K 𝔣 χ S s
        = ∑ i, α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧
      (∀ s : ℂ, 1 < s.re → completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s
        = ∑ i, α' i s * rayFoldMellin K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
            (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧
      (∀ i, ∀ s : ℂ, α' i s = α i (1 - s) * (1 / ((rayScale K 𝔣 (𝔞 i) : ℝ) : ℂ)) ^ S.card) ∧
      (∀ (x₀ : ι → K), (∀ i, IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) → χ ≠ 1 → ∀ s : ℂ,
        ∑ i, α i s * ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out a))
          * rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i)) = 0) ∧
      (∀ (x₀' : ι → K), (∀ i, IsCoprimeGenerator K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ)
          (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (x₀' i)) → χ ≠ 1 → ∀ s : ℂ,
        ∑ i, α' i s * ((∑ a : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
            (Quotient.out a))
          * rayInvPolarCoeff K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S
              (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i)) = 0) := by
  classical
  have hsurj : ∀ C : ClassGroup (𝓞 K), ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = C :=
    fun C => ClassGroup.induction (K := K)
      (P := fun C => ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = C) (fun I => ⟨I, rfl⟩) C
  choose 𝔞 h𝔞 using hsurj
  have hbij : Function.Bijective fun C => ClassGroup.mk K (𝔞 C) := by
    have h : (fun C => ClassGroup.mk K (𝔞 C)) = id := funext h𝔞
    rw [h]
    exact Function.bijective_id
  have hbij' := bijective_classGroup_mk_rayDualIdeal_comp K 𝔣 h𝔣 𝔞 hbij
  exact ⟨ClassGroup (𝓞 K), inferInstance, 𝔞, fun C => tc2Alpha K 𝔣 S (𝔞 C),
    fun C => tc2Alpha K 𝔣 S (rayDualIdeal K 𝔣 h𝔣 (𝔞 C)),
    fun C => differentiable_tc2Alpha K 𝔣 S (𝔞 C),
    fun C => differentiable_tc2Alpha K 𝔣 S (rayDualIdeal K 𝔣 h𝔣 (𝔞 C)),
    fun s hs => completedRayL_eq_sum_rayFoldMellin K 𝔣 χ S h𝔣 𝔞 hbij hs,
    fun s hs => completedRayL_eq_sum_rayFoldMellin K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S h𝔣
      (fun C => rayDualIdeal K 𝔣 h𝔣 (𝔞 C)) hbij' hs,
    fun C s => tc2Alpha_rayDualIdeal K 𝔣 S h𝔣 (𝔞 C) s,
    fun x₀ hx₀ hχ s => tc2Cancel K 𝔣 χ S hpar h𝔣 h𝔣' 𝔞 hbij x₀ hx₀ hχ s,
    fun x₀' hx₀' hχ s => tc2Cancel K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S (isParity_conj K hpar)
      h𝔣 h𝔣' (fun C => rayDualIdeal K 𝔣 h𝔣 (𝔞 C)) hbij' x₀' hx₀' (conjChar_ne_one K hχ) s⟩

section TopBranch

variable {K}

private def qZero (V s : ℂ) : ℂ := V / (s / 2)

private theorem differentiableOn_qZero (V : ℂ) : DifferentiableOn ℂ (qZero V) U01 := by
  show DifferentiableOn ℂ (fun s => V / (s / 2)) U01
  refine DifferentiableOn.div (differentiableOn_const V)
    (differentiable_id.div_const (2 : ℂ)).differentiableOn ?_
  intro s hs h
  rcases div_eq_zero_iff.mp h with h1 | h2
  · exact hs.1 h1
  · exact two_ne_zero h2

variable (K)
variable (ψ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ) (S : Finset {w : InfinitePlace K // IsReal w})

private def topThetaW (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : realSpace K) : ℂ :=
  (∑' z : {z : ↥(rayDualIdeal K ⊤ top_ne_bot 𝔞 : FractionalIdeal (𝓞 K)⁰ K) // (z : K) ≠ 0},
      (∏ v ∈ S, ((embedding_of_isReal v.2 (z.1 : K) : ℝ) : ℂ))
        * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
            * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ))
    * raySWeight K S t

private theorem topInvDual_eq (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K) (s : ℂ) (t : realSpace K) :
    topInvDual K ψ S 𝔞 x₀ s t
      = rayInvConst K ⊤ ψ S 𝔞 top_ne_bot x₀
          * (topThetaW K S 𝔞 t * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)) := by
  simp only [topInvDual, topThetaW, rayMellinWeight]
  ring

private def dualTopP (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K) (s : ℂ) : ℂ :=
  ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, topInvDual K ψ S 𝔞 x₀ s t ∂(torusHaar K)

private theorem top_dual_integrable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K) (s : ℂ) :
    IntegrableOn (topInvDual K ψ S 𝔞 x₀ s)
      (foldDomain K ∩ {t | 1 ≤ torusNorm K t}) (torusHaar K) := by
  obtain ⟨C, γ, hγ, h⟩ := exists_tail_bound_dualTheta₁ K ⊤ S 𝔞 top_ne_bot
  have h1 : Measurable (topThetaW K S 𝔞) := measurable_dualThetaW₁ K ⊤ S 𝔞 top_ne_bot
  have h2 : Measurable fun t : realSpace K => ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2) :=
    (Complex.measurable_ofReal.comp (measurable_torusNorm K)).pow_const _
  have hfun : topInvDual K ψ S 𝔞 x₀ s = fun t => rayInvConst K ⊤ ψ S 𝔞 top_ne_bot x₀
      * (topThetaW K S 𝔞 t * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)) :=
    funext (topInvDual_eq K ψ S 𝔞 x₀ s)
  have hmeas : Measurable (topInvDual K ψ S 𝔞 x₀ s) := by
    rw [hfun]
    exact (h1.mul h2).const_mul _
  refine integrableOn_highHalf_of_norm_le K hmeas.aestronglyMeasurable
    (‖rayInvConst K ⊤ ψ S 𝔞 top_ne_bot x₀‖ * C) hγ ((1 - s).re / 2) fun t ht => ?_
  have hN0 := torusNorm_pos_of_mem_highHalf K ht
  rw [topInvDual_eq, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN0,
    Complex.div_ofNat_re]
  have hb := h t ht
  rw [← topThetaW] at hb
  calc ‖rayInvConst K ⊤ ψ S 𝔞 top_ne_bot x₀‖
        * (‖topThetaW K S 𝔞 t‖ * torusNorm K t ^ ((1 - s).re / 2))
      ≤ ‖rayInvConst K ⊤ ψ S 𝔞 top_ne_bot x₀‖
        * (C * Real.exp (-γ * (torusNorm K t) ^ (Module.finrank ℚ K : ℝ)⁻¹)
          * torusNorm K t ^ ((1 - s).re / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hN0.le _))
          (norm_nonneg _)
    _ = _ := by ring

private theorem top_dual_differentiable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K) :
    Differentiable ℂ fun s =>
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, topInvDual K ψ S 𝔞 x₀ s t
        ∂(torusHaar K) := by
  obtain ⟨C, γ, hγ, h⟩ := exists_tail_bound_dualTheta₁ K ⊤ S 𝔞 top_ne_bot
  have hD := differentiable_setIntegral_highHalf_mul_cpow K
    (measurable_dualThetaW₁ K ⊤ S 𝔞 top_ne_bot) C hγ 0 (fun t ht => by simpa using h t ht)
  have hfun : (fun s => ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
        topInvDual K ψ S 𝔞 x₀ s t ∂(torusHaar K))
      = fun s => rayInvConst K ⊤ ψ S 𝔞 top_ne_bot x₀
          * ((fun s' : ℂ => ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
              topThetaW K S 𝔞 t * ((torusNorm K t : ℝ) : ℂ) ^ (s' / 2)
                ∂(torusHaar K)) (1 - s)) := by
    funext s
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_highHalf K) fun t _ =>
      topInvDual_eq K ψ S 𝔞 x₀ s t
  rw [hfun]
  exact (hD.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul _

private def contTop (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K) (P₀ V : ℂ) : ℂ → ℂ :=
  perIdeal (highP K ⊤ ψ S 𝔞) (dualTopP K ψ S 𝔞 x₀) (qOne V) (qZero V)
    (rayInvPolarCoeff K ⊤ ψ S 𝔞 top_ne_bot x₀) P₀

private theorem differentiableOn_contTop (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K) (P₀ V : ℂ) :
    DifferentiableOn ℂ (contTop K ψ S 𝔞 x₀ P₀ V) U01 :=
  differentiableOn_perIdeal
    (hole_high_differentiable K ⊤ ψ S 𝔞 top_ne_bot (rayScale_pos K ⊤ top_ne_bot 𝔞))
    (top_dual_differentiable K ψ S 𝔞 x₀) (differentiableOn_qOne V)
    (differentiableOn_qZero V)

private theorem contTop_eq {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x₀ : K} {P₀ V : ℂ}
    (hinv : ∀ t ∈ orthant K, ∀ s : ℂ,
      rayFoldMellinIntegrand K ⊤ ψ S 𝔞 (rayScale K ⊤ 𝔞) s t⁻¹
        = topInvDual K ψ S 𝔞 x₀ s t
          + rayInvPolarCoeff K ⊤ ψ S 𝔞 top_ne_bot x₀ * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
          + P₀ * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2))
    (hV : ∀ z : ℂ, 0 < z.re →
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z)
        ∂(torusHaar K) = V / z)
    {s : ℂ} (hs : 1 < s.re) :
    contTop K ψ S 𝔞 x₀ P₀ V s = rayFoldMellin K ⊤ ψ S 𝔞 (rayScale K ⊤ 𝔞) s := by
  have hc : 0 < rayScale K ⊤ 𝔞 := rayScale_pos K ⊤ top_ne_bot 𝔞
  have hz : ((1 - s) / 2).re < 0 := by
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hz' : 0 < ((s - 1) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hz0 : (-s / 2).re < 0 := by
    rw [Complex.div_ofNat_re, Complex.neg_re]
    linarith
  have hz0' : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  have hI1 := (hole_polar_integrable K hz).const_mul (rayInvPolarCoeff K ⊤ ψ S 𝔞 top_ne_bot x₀)
  have hI0 := (hole_polar_integrable K hz0).const_mul P₀
  have hsplit := rayFoldMellin_split_of_inv K ⊤ ψ S 𝔞 (rayScale K ⊤ 𝔞) s
    (topInvDual K ψ S 𝔞 x₀ s) 1
    (fun t => rayInvPolarCoeff K ⊤ ψ S 𝔞 top_ne_bot x₀ * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
      + P₀ * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2))
    (integrableOn_foldDomain_rayFoldMellinIntegrand K ⊤ ψ S 𝔞 top_ne_bot _ hc hs)
    (top_dual_integrable K ψ S 𝔞 x₀ s) (hI1.add hI0)
    (fun t ht => by rw [hinv t ht s, one_mul, add_assoc])
  have hpol : ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t},
      (rayInvPolarCoeff K ⊤ ψ S 𝔞 top_ne_bot x₀ * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
        + P₀ * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2)) ∂(torusHaar K)
      = rayInvPolarCoeff K ⊤ ψ S 𝔞 top_ne_bot x₀ * qOne V s + P₀ * qZero V s := by
    rw [integral_add hI1 hI0, integral_const_mul, integral_const_mul]
    have h1 := hV _ hz'
    rw [show -((s - 1) / 2) = (1 - s) / 2 by ring] at h1
    have h0 := hV _ hz0'
    rw [show -(s / 2) = -s / 2 by ring] at h0
    rw [h1, h0, qOne, qZero]
  rw [contTop, perIdeal, hsplit, hpol, one_mul]
  unfold highP dualTopP
  ring

variable {ψ S}

private theorem wallHalf_top {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : ι → K)
    (P₀ : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℂ)
    (hinv : ∀ i, ∀ t ∈ orthant K, ∀ s : ℂ,
      rayFoldMellinIntegrand K ⊤ ψ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s t⁻¹
        = topInvDual K ψ S (𝔞 i) (x₀ i) s t
          + rayInvPolarCoeff K ⊤ ψ S (𝔞 i) top_ne_bot (x₀ i)
              * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
          + P₀ (𝔞 i) * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2))
    (α : ι → ℂ → ℂ) (hα : ∀ i, Differentiable ℂ (α i)) (Λ : ℂ → ℂ)
    (hT : ∀ s : ℂ, 1 < s.re → Λ s = ∑ i, α i s * rayFoldMellin K ⊤ ψ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)
    {V : ℂ} (hV : ∀ z : ℂ, 0 < z.re →
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z)
        ∂(torusHaar K) = V / z) :
    DifferentiableOn ℂ (fun s => ∑ i, α i s * contTop K ψ S (𝔞 i) (x₀ i) (P₀ (𝔞 i)) V s) U01 ∧
    ∀ s : ℂ, 1 < s.re → (∑ i, α i s * contTop K ψ S (𝔞 i) (x₀ i) (P₀ (𝔞 i)) V s) = Λ s :=
  ⟨differentiableOn_sum_mul α _ hα fun i => differentiableOn_contTop K ψ S (𝔞 i) (x₀ i) (P₀ (𝔞 i)) V,
   fun _ hs => sum_mul_eq_of_eq α _ (fun i s => rayFoldMellin K ⊤ ψ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) Λ
     (fun i _ hs => contTop_eq K ψ S (hinv i) hV hs) hT hs⟩

private theorem wallConj_top (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w})
    {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x₀ x₀' : ι → K) (α : ι → ℂ → ℂ) (hα : ∀ i, Differentiable ℂ (α i))
    (P₀ P₀' : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℂ)
    (hinv : ∀ i, ∀ t ∈ orthant K, ∀ s : ℂ,
      rayFoldMellinIntegrand K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s t⁻¹
        = topInvDual K χ S (𝔞 i) (x₀ i) s t
          + rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)
              * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
          + P₀ (𝔞 i) * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2))
    (hinv' : ∀ i, ∀ t ∈ orthant K, ∀ s : ℂ,
      rayFoldMellinIntegrand K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i)
          (rayScale K ⊤ (𝔞 i)) s t⁻¹
        = topInvDual K ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) (x₀' i) s t
          + rayInvPolarCoeff K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) top_ne_bot (x₀' i)
              * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
          + P₀' (𝔞 i) * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2))
    (hT : ∀ s : ℂ, 1 < s.re → completedRayL K ⊤ χ S s
      = ∑ i, α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)
    (hT' : ∀ s : ℂ, 1 < s.re → completedRayL K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S s
      = ∑ i, α i s * rayFoldMellin K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i)
          (rayScale K ⊤ (𝔞 i)) s)
    (hcancel : χ ≠ 1 → ∀ s : ℂ,
      (∑ i, α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) = 0 ∧
      (∑ i, α i s * P₀ (𝔞 i)) = 0)
    (hcancel' : χ ≠ 1 → ∀ s : ℂ,
      (∑ i, α i s * rayInvPolarCoeff K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) top_ne_bot
        (x₀' i)) = 0 ∧
      (∑ i, α i s * P₀' (𝔞 i)) = 0) :
    ∃ F G : ℂ → ℂ, WallConj K ⊤ χ S F G := by
  obtain ⟨V, hV⟩ := hole_polar_eval K
  have hV' : ∀ z : ℂ, 0 < z.re →
      ∫ t in foldDomain K ∩ {t | 1 ≤ torusNorm K t}, ((torusNorm K t : ℝ) : ℂ) ^ (-z)
        ∂(torusHaar K) = V / z := fun z hz => hV hz
  obtain ⟨hF1, hF3⟩ := wallHalf_top K 𝔞 x₀ P₀ hinv α hα (fun s => completedRayL K ⊤ χ S s) hT hV'
  obtain ⟨hG1, hG3⟩ := wallHalf_top K 𝔞 x₀' P₀' hinv' α hα
    (fun s => completedRayL K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S s) hT' hV'
  refine ⟨fun s => ∑ i, α i s * contTop K χ S (𝔞 i) (x₀ i) (P₀ (𝔞 i)) V s,
    fun s => ∑ i, α i s * contTop K ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) (x₀' i)
      (P₀' (𝔞 i)) V s, ?_⟩
  unfold WallConj
  refine ⟨hF1, hG1, hF3, hG3, fun _ h𝔣' => absurd rfl h𝔣', fun hχ => ⟨?_, ?_⟩⟩
  · exact differentiable_sum_mul_perIdeal_of_cancel α (fun i => highP K ⊤ χ S (𝔞 i))
      (fun i => dualTopP K χ S (𝔞 i) (x₀ i)) (qOne V) (qZero V)
      (fun i => rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) (fun i => P₀ (𝔞 i)) hα
      (fun i => hole_high_differentiable K ⊤ χ S (𝔞 i) top_ne_bot (rayScale_pos K ⊤ top_ne_bot (𝔞 i)))
      (fun i => top_dual_differentiable K χ S (𝔞 i) (x₀ i))
      (hcancel hχ)
  · exact differentiable_sum_mul_perIdeal_of_cancel α
      (fun i => highP K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i))
      (fun i => dualTopP K ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) (x₀' i))
      (qOne V) (qZero V)
      (fun i => rayInvPolarCoeff K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) top_ne_bot (x₀' i))
      (fun i => P₀' (𝔞 i)) hα
      (fun i => hole_high_differentiable K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) top_ne_bot
        (rayScale_pos K ⊤ top_ne_bot (𝔞 i)))
      (fun i => top_dual_differentiable K ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i)
        (x₀' i))
      (hcancel' hχ)

end TopBranch
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

private theorem hole_top (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K ⊤ χ S) :
    ∃ (ι : Type) (_ : Fintype ι) (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : ι → ℂ → ℂ)
      (P₀ P₀' : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℂ),
      (∀ i, Differentiable ℂ (α i)) ∧
      (∀ s : ℂ, 1 < s.re → completedRayL K ⊤ χ S s
        = ∑ i, α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧
      (∀ s : ℂ, 1 < s.re → completedRayL K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S s
        = ∑ i, α i s * rayFoldMellin K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i)
            (rayScale K ⊤ (𝔞 i)) s) ∧
      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K), IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →
        ∀ t ∈ orthant K, ∀ s : ℂ,
          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹
            = topInvDual K χ S 𝔟 x₀ s t
              + rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
              + P₀ 𝔟 * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2)) ∧
      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),
        IsCoprimeGenerator K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) 𝔟 x₀ →
        ∀ t ∈ orthant K, ∀ s : ℂ,
          rayFoldMellinIntegrand K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹
            = topInvDual K ((starRingEnd ℂ).toMonoidHom.comp χ) S 𝔟 x₀ s t
              + rayInvPolarCoeff K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S 𝔟 top_ne_bot x₀
                  * ((torusNorm K t : ℝ) : ℂ) ^ ((1 - s) / 2)
              + P₀' 𝔟 * ((torusNorm K t : ℝ) : ℂ) ^ (-s / 2)) ∧
      (χ ≠ 1 → ∀ (x₀ : ι → K), (∀ i, IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) → ∀ s : ℂ,
        (∑ i, α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) = 0 ∧
        (∑ i, α i s * P₀ (𝔞 i)) = 0) ∧
      (χ ≠ 1 → ∀ (x₀' : ι → K),
        (∀ i, IsCoprimeGenerator K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) (𝔞 i) (x₀' i)) → ∀ s : ℂ,
        (∑ i, α i s * rayInvPolarCoeff K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S (𝔞 i) top_ne_bot
          (x₀' i)) = 0 ∧
        (∑ i, α i s * P₀' (𝔞 i)) = 0) := by
  classical
  have hsurj : ∀ C : ClassGroup (𝓞 K), ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = C :=
    fun C => ClassGroup.induction (K := K)
      (P := fun C => ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = C) (fun I => ⟨I, rfl⟩) C
  choose 𝔞 h𝔞 using hsurj
  have hbij : Function.Bijective fun C => ClassGroup.mk K (𝔞 C) := by
    have h : (fun C => ClassGroup.mk K (𝔞 C)) = id := funext h𝔞
    rw [h]
    exact Function.bijective_id
  exact ⟨ClassGroup (𝓞 K), inferInstance, 𝔞, fun C => tc2Alpha K ⊤ S (𝔞 C),
    topInvPolar0 K χ S, topInvPolar0 K ((starRingEnd ℂ).toMonoidHom.comp χ) S,
    fun C => differentiable_tc2Alpha K ⊤ S (𝔞 C),
    fun s hs => completedRayL_eq_sum_rayFoldMellin K ⊤ χ S top_ne_bot 𝔞 hbij hs,
    fun s hs => completedRayL_eq_sum_rayFoldMellin K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S
      top_ne_bot 𝔞 hbij hs,
    fun 𝔟 x₀ hx₀ t ht s => rayFoldMellinIntegrand_inv_top K χ S hpar 𝔟 hx₀ ht s,
    fun 𝔟 x₀ hx₀ t ht s => rayFoldMellinIntegrand_inv_top K ((starRingEnd ℂ).toMonoidHom.comp χ) S
      (isParity_conj K hpar) 𝔟 hx₀ ht s,
    fun hχ x₀ hx₀ s => tc2CancelTop K χ S hpar 𝔞 hbij x₀ hx₀ hχ s,
    fun hχ x₀' hx₀' s => tc2CancelTop K ((starRingEnd ℂ).toMonoidHom.comp χ) S (isParity_conj K hpar)
      𝔞 hbij x₀' hx₀' (conjChar_ne_one K hχ) s⟩

private theorem fe_of_ne_bot (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K 𝔣 χ S) (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ F G : ℂ → ℂ, WallConj K 𝔣 χ S F G := by
  by_cases h𝔣' : 𝔣 = ⊤
  · subst h𝔣'
    obtain ⟨ι, _, 𝔞, α, P₀, P₀', hα, hT, hT', hinv, hinv', hcancel, hcancel'⟩ := hole_top K χ S hpar
    choose x₀ hx₀ using fun i => exists_isCoprimeGenerator K ⊤ χ (𝔞 i) top_ne_bot
    choose x₀' hx₀' using fun i =>
      exists_isCoprimeGenerator K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) (𝔞 i) top_ne_bot
    exact wallConj_top K χ S 𝔞 x₀ x₀' α hα P₀ P₀' (fun i => hinv (𝔞 i) (x₀ i) (hx₀ i))
      (fun i => hinv' (𝔞 i) (x₀' i) (hx₀' i)) hT hT' (fun hχ => hcancel hχ x₀ hx₀)
      (fun hχ => hcancel' hχ x₀' hx₀')
  · haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
    letI : Fintype (𝓞 K ⧸ 𝔣) := Fintype.ofFinite _
    obtain ⟨ι, _, 𝔞, α, α', hα, hα', hT, hT', hαα', hcancel, hcancel'⟩ :=
      hole_T2 K 𝔣 χ S hpar h𝔣 h𝔣'
    choose x₀ hx₀ using fun i => exists_isCoprimeGenerator K 𝔣 χ (𝔞 i) h𝔣
    choose x₀' hx₀' using fun i =>
      exists_isCoprimeGenerator K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣
    exact wallConj_of_T2 K 𝔣 χ S hpar h𝔣 h𝔣' 𝔞 x₀ hx₀ x₀' hx₀' α α' hα hα' hT hT' hαα'
      (hcancel x₀ hx₀) (hcancel' x₀' hx₀')

private theorem completedRayL_fe_impl
    (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ F G : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      DifferentiableOn ℂ G {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      (∀ s : ℂ, 1 < s.re → F s = completedRayL K 𝔣 χ S s) ∧
      (∀ s : ℂ, 1 < s.re →
        G s = completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ h𝔣 : 𝔣 ≠ ⊥, ∀ h𝔣' : 𝔣 ≠ ⊤, ∀ y₀ : K, M4aP2.IsGaussDatum K 𝔣 χ y₀ →
        M4aP2.IsPrimitiveMod K 𝔣 χ →
        ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
          F (1 - s) = (-Complex.I) ^ S.card *
            (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) * G s) ∧
      (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G) := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣
    refine ⟨fun _ => 0, fun _ => 0, differentiableOn_const _, differentiableOn_const _,
      ?_, ?_, ?_, ?_⟩
    · intro s hs
      exact (completedRayL_bot K χ S (ne_zero_of_one_lt_re hs)).symm
    · intro s hs
      exact (completedRayL_bot K _ S (ne_zero_of_one_lt_re hs)).symm
    · intro h
      exact absurd rfl h
    · intro _
      exact ⟨differentiable_const _, differentiable_const _⟩
  · obtain ⟨F, G, h⟩ := fe_of_ne_bot K 𝔣 χ S hpar h𝔣
    exact ⟨F, G, h⟩

end Assembly
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end M4aTorus.WallSol
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.WallSol"
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus"

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.WallSol"

end TcFold_SKELETON
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.WallSol"

set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace Complex Deep.NTSupply nonZeroDivisors

open _root_.M4aTorus _root_.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ F G : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      DifferentiableOn ℂ G {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      (∀ s : ℂ, 1 < s.re → F s = completedRayL K 𝔣 χ S s) ∧
      (∀ s : ℂ, 1 < s.re →
        G s = completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ h𝔣 : 𝔣 ≠ ⊥, ∀ h𝔣' : 𝔣 ≠ ⊤, ∀ y₀ : K, M4aP2.IsGaussDatum K 𝔣 χ y₀ →
        M4aP2.IsPrimitiveMod K 𝔣 χ →
        ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
          F (1 - s) = (-Complex.I) ^ S.card *
            (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) * G s) ∧
      (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G) :=
  M4aTorus.WallSol.completedRayL_fe_impl K 𝔣 χ S hpar

end
p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aTorus P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.WallSol"

end S_M4aTorus_completedRayL_fe
end P2MW
export P2MW.S_M4aTorus_completedRayL_fe (solution)
