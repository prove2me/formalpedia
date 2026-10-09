-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstNestedSeededGaussianPower.nested_source_descent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:38:37.006069+00:00
-- url     : https://prove2.me/submissions/69089f2a-4b3d-4580-8f1f-17ddb851eb6b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondExceptionalFamily_exists_exceptional_family
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondFrozenChosen_actual_canonical_children
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondNonexceptionalAggregate_source_part_harmonic_bound
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondSourceRemainder_original_source_remainder

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

open FirstPassCubeLabels

lemma weighted_schwartz_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  simpa using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J

end JointLogSeparation

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Support
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

theorem support_reconstruct (I : Ideal O) (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorAllocation
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem squarefree_dvd_iff (D I : Ideal O) (hD : Squarefree D) :
    D∣I ↔ ∀ P ∈ primeSupport D,P∣I := by
  constructor
  · intro hd P hP
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hd
  · intro h
    rw [← squarefree_support_product_self hD]
    apply Finset.prod_dvd_of_coprime ?_ h
    intro P hP Q hQ hne
    let : P.IsMaximal := (Ideal.isPrime_of_prime (support_prime hP)).isMaximal (support_prime hP).ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime (support_prime hQ)).isMaximal (support_prime hQ).ne_zero
    exact Ideal.isCoprime_of_isMaximal hne

end SevenEighths.CenteredMomentDivisorAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RankinRadical
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinRadical
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O

theorem old_mask_dvd_commonRadical (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J := by
  apply (squarefree_dvd_iff s _ hs).mpr
  intro P hP
  have hp := support_prime hP
  have hd := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  have hi : P ∈ primeSupport I := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hI,hp,true_and]
      using hd.trans hsI
  have hj : P ∈ primeSupport J := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hJ,hp,true_and]
      using hd.trans hsJ
  exact Finset.dvd_prod_of_mem id (Finset.mem_inter.mpr ⟨hi,hj⟩)

end SevenEighths.CenteredMomentRankinRadical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CompleteCommon
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem commonPart_ne_zero (I J : Ideal O) : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem commonParts_equal_support (I J : Ideal O) :
    primeSupport (commonPart I J) = primeSupport (commonPart J I) := by
  rw [commonPart_support, commonPart_support, commonSupport_comm I J]

theorem commonPart_dvd (I J : Ideal O) (hI : I ≠ 0) : commonPart I J ∣ I :=
  ⟨residualPart I J, reconstruct I J hI⟩

theorem commonRadical_dvd_commonPart (I J : Ideal O) : commonRadical I J ∣ commonPart I J := by
  apply support_product_dvd (commonPart_ne_zero I J)
  rw [commonPart_support]
  exact Finset.Subset.refl _

theorem absNorm_commonPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (commonPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (commonPart_dvd I J hI))

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeColumnWindow
open FourierBridge HeckeFamily CenteredMomentSmooth CenteredMomentGaussEnergy
open CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem columnDensity_moments (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (J : ℕ) :
    Integrable (fun w : ℝ => (1+‖w‖)^J*‖columnDensity V hVc hVs w‖) :=
  JointLogSeparation.weighted_schwartz_integrable _ J

end SevenEighths.CenteredMomentHeckeColumnWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AddedZeroUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceMass
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceMass
open CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma profileProduct_mem_box {r : ℕ} (W : Fin r → ℝ → ℂ) (b q : Fin r → ℝ)
    (hq : ∀ i, 0<q i) (hzero : ∀ i, W i 0=0)
    (hs : ∀ i x, W i x ≠ 0 → x ≤ b i)
    (v : Fin r → Ideal O) (hv : profileProduct W q v ≠ 0) :
    v ∈ tupleBox (fun i => b i*q i) := by
  apply (mem_tupleBox _ _).mpr
  intro i
  have hw : W i ((Ideal.absNorm (v i):ℝ)/q i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hv) i (Finset.mem_univ i)
  refine ⟨?_,(div_le_iff₀ (hq i)).mp (hs i _ hw)⟩
  intro hz
  apply hw
  simp only [hz,map_zero,Nat.cast_zero,zero_div,hzero]

lemma sourceProfiles_product {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O) :
    profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v =
      (∏ j : Fin N, Wslot j ((Ideal.absNorm (v (j.castAdd 2)):ℝ)/P j)) *
      (W₁ ((Ideal.absNorm (B₁*v ⟨N,by omega⟩):ℝ)/X₁) *
       W₂ ((Ideal.absNorm (B₂*v ⟨N+1,by omega⟩):ℝ)/X₂)) := by
  simp only [profileProduct,Fin.prod_univ_add,sourceProfiles,sourceScales,
    Fin.append_left,Fin.append_right,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_mul,Nat.cast_mul,div_div_eq_mul_div]
  have h₀ : Fin.natAdd N (0:Fin 2)=⟨N,by omega⟩ := by ext; simp
  have h₁ : Fin.natAdd N (1:Fin 2)=⟨N+1,by omega⟩ := by ext; simp
  rw [h₀,h₁]
  congr 2 <;> congr 1 <;> ring

lemma sourceBounds_product {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) :
    (∏ i, sourceBounds b b₁ b₂ i) = (∏ j,b j)*b₁*b₂ := by
  simp only [sourceBounds,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_product {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∏ i, sourceScales P X₁ X₂ B₁ B₂ i) =
      (∏ j,P j)*(X₁*X₂)/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂) := by
  simp only [sourceScales,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_pos {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : B₁≠0) (hB₂ : B₂≠0) :
    ∀ i, 0<sourceScales P X₁ X₂ B₁ B₂ i := by
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  simp only [Fin.forall_fin_add,sourceScales,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hP,div_pos hX₁ hn₁,div_pos hX₂ hn₂⟩

theorem originalCoefficient_factor (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v =
      (∏ j,ν j (v (j.castAdd 2))) * idealWeight c χ R t (tupleProduct v) *
      (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v -
       profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v) *
      (if s∣tupleProduct v then 1 else 0) := by
  rw [originalCoefficient,Finset.prod_mul_distrib,sourceProfiles_product,sourceProfiles_product]
  unfold idealRectangle
  ring

lemma sourcePool_nonzero {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) : tupleProduct v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h <;>
    exact ((mem_tupleBox _ _).mp h i).1

theorem originalCoefficient_mem_sourcePool (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v ≠ 0) :
    v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [originalCoefficient_factor] at hv
  have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
  have hd := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  apply Finset.mem_filter.mpr
  refine ⟨?_,fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)⟩
  apply Finset.mem_union.mpr
  by_cases hx : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v = 0
  · apply Or.inr
    have hy : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v ≠ 0 := by
      intro hy; exact hd (by rw [hx,hy,sub_self])
    exact profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂) hzero hs v hy
  · exact Or.inl (profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂) hzero hs v hx)

lemma source_coordinate_product {N : ℕ} (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ T : ℝ) (B₁ B₂ : Ideal O) (hT : X₁*X₂=T) :
    (∏ i,sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i) =
      sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rw [Finset.prod_mul_distrib,sourceBounds_product,sourceScales_product,hT]
  unfold sourceRadius
  ring

lemma tupleBox_product_bound {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O)
    (hv : v ∈ tupleBox H) : (Ideal.absNorm (tupleProduct v):ℝ) ≤ ∏ i,H i := by
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => ((mem_tupleBox H v).mp hv i).2)

theorem sourcePool_product_bound {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (Ideal.absNorm (tupleProduct v):ℝ) ≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hx|hy
  · exact (tupleBox_product_bound _ v hx).trans_eq (source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX)
  · exact (tupleBox_product_bound _ v hy).trans_eq (source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY)

theorem originalCoefficient_product_bound (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    tupleProduct v≠0 ∧ (Ideal.absNorm (tupleProduct v):ℝ)≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hm⟩

open CenteredMomentAddedZeroUniform

end SevenEighths.CenteredMomentSourceMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceProfileMass
open ActualEisensteinCubic CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
local notation "O" => ActualEisensteinCubic.O

 theorem primary_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (I : Ideal O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:O)}) (CompletedGauss.primaryGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (R I : Ideal O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PartitionNorm
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartitionNorm
open CenteredMomentPartition CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem unitIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (U : Finset ι) : 0 < (Ideal.absNorm (unitIdeal p U) : ℝ) := by
  simp only [unitIdeal, map_prod, Nat.cast_prod]
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

theorem partitionNormalizer_mul_unit_norm (p : ι → O) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U * (Ideal.absNorm (unitIdeal p U) : ℝ) =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [unitIdeal, commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  have hU : (∏ i ∈ U, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∏ i, if i ∈ U then (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 1 := by simp
  rw [hU, partitionNormalizer, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : i ∈ U
  · simp only [if_pos hmem]
    rw [← pow_succ, Nat.sub_add_cancel (le_min (hc i) (hd i))]
  · simp only [if_neg hmem, Nat.sub_zero, mul_one]

theorem partitionNormalizer_eq_norm_ratio (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) / Ideal.absNorm (unitIdeal p U) := by
  apply (eq_div_iff (unitIdeal_norm_pos p hp U).ne').mpr
  exact partitionNormalizer_mul_unit_norm p c d hc hd U

end SevenEighths.CenteredMomentPartitionNorm

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceZeroEnergy
open ActualEisensteinCubic HeckeFamily CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy
open CenteredMomentFirstLocalization CenteredMomentSourceRow
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem profileCoefficient_product_bound {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ)
    (P b : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hz : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀ j x,Wslot j x≠0 → x≤b j)
    (hs₁ : ∀ x,W₁ x≠0 → x≤b₁) (hs₂ : ∀ x,W₂ x≠0 → x≤b₂)
    (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤
      (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (e.symm j)) (And.intro hz₁ hz₂)
  have hsup : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0 →
      x≤ sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hs (e.symm j)) (And.intro hs₁ hs₂)
  have hn : CenteredMomentAddedZero.originalCoefficient (Fintype.card ι) 1
      (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tupleEquiv e v)≠0 := by
    rw [originalCoefficient_reindex,←profileCoefficient_eq_original]
    exact hv
  have hh := originalCoefficient_product_bound (Fintype.card ι) 1
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j => Wslot (e.symm j)) (fun j => P (e.symm j)) (fun j => b (e.symm j))
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP (e.symm j))
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hsup (tupleEquiv e v) hn
  simpa only [tupleProduct_reindex,sourceRadius,e.symm.prod_comp] using hh

end SevenEighths.CenteredMomentSourceZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ActiveSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentActiveSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem supportedColumns_active (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    supportedColumns (activeSource S β)=(supportedColumns S).filter (fun I => β I≠0) := by
  ext I
  simp only [supportedColumns,activeSource,Finset.mem_filter]
  tauto

theorem commonLabel_witnesses (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    ∃I∈S,∃J∈S,Supported I ∧ Supported J ∧ β I≠0 ∧ β J≠0 ∧
      commonPart I J=C ∧ commonPart J I=D := by
  obtain ⟨⟨I,J⟩,hp,he⟩ := Finset.mem_image.mp h
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  obtain ⟨hi,hIs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hJs⟩ := Finset.mem_filter.mp hj
  obtain ⟨hi,hβi⟩ := mem_activeSource S β I |>.mp hi
  obtain ⟨hj,hβj⟩ := mem_activeSource S β J |>.mp hj
  exact ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,(Prod.mk.inj he).1,(Prod.mk.inj he).2⟩

theorem commonLabel_norm_bounds (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    (Ideal.absNorm C:ℝ)≤H ∧ (Ideal.absNorm D:ℝ)≤H := by
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β C D h
  constructor
  · rw [←hC]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le I J hIs.1)).trans (hH I hi hβi)
  · rw [←hD]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le J I hJs.1)).trans (hH J hj hβj)

end SevenEighths.CenteredMomentActiveSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.EligibleEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma Data.profile_nonneg (s:Data ι) : 0≤ s.profileFactor :=by
  unfold Data.profileFactor
  exact mul_nonneg (by positivity) (sq_nonneg _)

end SevenEighths.CenteredMomentEligibleEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRadialPointwise
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma profileCost_nonneg (s:Input ι) : 0≤profileCost s :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) s.toData.profile_nonneg

end SevenEighths.CenteredMomentCommonRadialPointwise

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonical
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)

theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalLedger
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentForcing
local notation "O" => ActualEisensteinCubic.O

theorem span_finset_product {ι : Type*} (S : Finset ι) (p : ι→O) :
    Ideal.span {∏ i∈S,p i}=∏ i∈S,Ideal.span {p i} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,
      ←Ideal.span_singleton_mul_span_singleton,ih]

theorem commonFrequencyGenerator_span (C D : Ideal O) (_hC : Supported C) :
    Ideal.span {commonFrequencyGenerator C D}=
      commonIdeal (commonPrime C D) (leftExponent C D) (rightExponent C D) := by
  simp only [commonFrequencyGenerator,span_finset_product,←Ideal.span_singleton_pow,commonIdeal]

theorem actual_partitionNormalizer (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U=
      (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/
        Ideal.absNorm (∏ P∈U,P.val) := by
  rw [partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D),←commonFrequencyGenerator_span C D hC]
  simp only [unitIdeal,commonPrime_span C D hC]

end SevenEighths.CenteredMomentSecondCanonicalLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowBudget
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy

theorem profileMoment_nonneg (J : ℕ) : 0≤profileMoment J :=
  integral_nonneg (fun w=>by positivity)

theorem heightEnvelope_pos (t : ℝ) : 0<heightEnvelope t := by unfold heightEnvelope;positivity

end SevenEighths.CenteredMomentSecondWindowBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceDyadicShell
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceDyadicShell
open CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma residual_window_bounds (C I:Ideal O) (hC:C≠0) (L U:ℝ) (n:ℤ)
    (hL:L≤(Ideal.absNorm (C*I):ℝ)) (hU:(Ideal.absNorm (C*I):ℝ)≤U)
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    L/(Ideal.absNorm C:ℝ)≤dyadicScale n ∧
      dyadicScale n≤4*U/(Ideal.absNorm C:ℝ) := by
  have hc:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=dyadicWeight_support n hw
  simp only [map_mul,Nat.cast_mul] at hL hU
  constructor
  · apply (div_le_iff₀ hc).mpr
    exact hL.trans (by nlinarith [hs.2])
  · apply (le_div_iff₀ hc).mpr
    nlinarith [hs.1]

end SevenEighths.CenteredMomentSourceDyadicShell

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceBlockWindows
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceBlockWindows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

 theorem physicalBlock_column_witnesses (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃I:sectorPool C hC.1 S,∃J:sectorPool D hD.1 S,
      β (C*I)≠0 ∧ β (D*J)≠0 ∧
      dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)≠0 ∧
      dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ)≠0 := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hcoeff: (β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J)≠0:=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).1).2
    have hl:β (C*I)≠0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hcoeff).1).1
    have hr:β (D*J)≠0:=by
      intro hh
      exact hcoeff (by rw [hh,zero_mul,star_zero,mul_zero])
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact ⟨I,J,hl,hr,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2,(mul_ne_zero_iff.mp hw).2⟩
  · exact False.elim (hz rfl)

end SevenEighths.CenteredMomentSourceBlockWindows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondPhysicalLedger
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
lemma profileFactor_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor Sprofile s p J Q K:=by
  unfold profileFactor
  have hp:=Profiles.control_nonneg p Sprofile
  positivity

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondActiveCount
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActiveCount
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
open CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

theorem active_common_data (S : Finset (Ideal O)) (β : Ideal O→ℂ) (s : Ideal O)
    (hs : Squarefree s) (hmask : ∀I∈S,β I≠0 → s∣I) (Y : ℝ)
    (p : Ideal O×Ideal O) (hp : p∈commonShell S β Y) :
    p.1≠0 ∧ p.2≠0 ∧ CompletedGauss.primeSupport p.1=CompletedGauss.primeSupport p.2 ∧
      s∣p.1 ∧ s∣p.2 := by
  have hm := (Finset.mem_filter.mp hp).1
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β p.1 p.2 hm
  have hsR := old_mask_dvd_commonRadical s I J hs hIs.1 hJs.1 (hmask I hi hβi) (hmask J hj hβj)
  refine ⟨hC ▸ commonPart_ne_zero I J,hD ▸ commonPart_ne_zero J I,?_,?_,?_⟩
  · rw [←hC,←hD]
    exact commonParts_equal_support I J
  · rw [←hC]
    exact hsR.trans (commonRadical_dvd_commonPart I J)
  · rw [←hD]
    have hr : commonRadical I J=commonRadical J I := by unfold commonRadical;rw [Finset.inter_comm]
    rw [hr] at hsR
    exact hsR.trans (commonRadical_dvd_commonPart J I)

end SevenEighths.CenteredMomentSecondActiveCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentOriginalCommonHarmonic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentSecondActiveCount CenteredMomentActiveSource CenteredMomentCommonHarmonicMass
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentOriginalCommonHarmonic.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
 theorem original_column_mask (s:Input ι) (R seed I:Ideal O) (h:coefficient s R seed I≠0):
    seed∣I:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [profileCoefficient,hn,ite_false,mul_zero]

omit [DecidableEq ι] in
 theorem original_column_norm (s:Input ι) (R seed I:Ideal O)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (h:coefficient s R seed I≠0):
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤ sourceRadius s:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    have hh:=(s.support i hn).1
    linarith [s.lo_pos i]
  have hh:=profileCoefficient_product_bound R s.ν s.W s.P s.hi s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product hz hz₁ hz₂
    (fun i x hx=>(s.support i hx).2) (fun x hx=>s.support₁ hx) (fun x hx=>s.support₂ hx) v hv0
  rw [he] at hh
  simpa only [sourceRadius,map_one,Nat.cast_one,mul_one,div_one] using hh

omit [DecidableEq ι] in
 theorem actual_common_gates (s:Input ι) (R seed:Ideal O) (hs:Squarefree seed)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (C D:Ideal O)
    (hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))):
    C≠0 ∧ D≠0 ∧ CompletedGauss.primeSupport C=CompletedGauss.primeSupport D ∧
      seed∣C ∧ seed∣D ∧ (Ideal.absNorm C:ℝ)≤ sourceRadius s ∧ (Ideal.absNorm D:ℝ)≤ sourceRadius s:=by
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s R seed I hI
  have hp:(C,D)∈commonShell S β (Ideal.absNorm (CenteredMomentRankinRadical.commonRadical C D):ℝ):=
    Finset.mem_filter.mpr ⟨hlabel,le_rfl⟩
  have hh:=active_common_data S β seed hs hm _ (C,D) hp
  have hn:=commonLabel_norm_bounds S β (sourceRadius s)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2) C D hlabel
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hn⟩

end SevenEighths.CenteredMomentOriginalCommonHarmonic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputTailUniform.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
lemma volume_pos (s:Input ι):0<volume s.toData:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentSourceInputTailUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondActivePhysicalDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondActivePhysicalDictionary
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentSecondSectorFrequency CenteredMomentActiveSource
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSecondSectorRetained CenteredMomentSmooth
local notation "O"=>HeckeFamily.O

 theorem sectorPool_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β:Ideal O→ℂ):
    sectorPool C hC (activeSource S β)=(sectorPool C hC S).filter (fun I=>β (C*I)≠0):=by
  ext I
  simp only [sectorPool,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

 theorem sector_sum_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β f:Ideal O→ℂ)
    (hf:∀I,β (C*I)=0→f I=0):
    (∑I∈sectorPool C hC (activeSource S β),f I)=∑I∈sectorPool C hC S,f I:=by
  rw [sectorPool_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h:β (C*I)=0
  · simp only [h,ne_eq,not_true_eq_false,ite_false,hf I h]
  · simp only [h,ne_eq,not_false_eq_true,ite_true]

 theorem sector_pair_sum_active (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(f:Ideal O→Ideal O→ℂ)
    (hleft:∀I J,β (C*I)=0→f I J=0)(hright:∀I J,β (D*J)=0→f I J=0):
    (∑I∈sectorPool C hC (activeSource S β),∑J∈sectorPool D hD (activeSource S β),f I J)=
      ∑I∈sectorPool C hC S,∑J∈sectorPool D hD S,f I J:=by
  simp_rw [sector_sum_active D hD S β _ (fun J h=>hright _ J h)]
  apply sector_sum_active C hC S β
  intro I h
  exact Finset.sum_eq_zero (fun J hJ=>hleft I J h)

 theorem sectorFrequency_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(F:O→Ideal O→Ideal O→ℂ)(z:O):
    sectorFrequency η t S β C D hC hD F z=
      sectorFrequency η t (activeSource S β) β C D hC hD F z:=by
  let f:Ideal O→Ideal O→ℂ:=fun I J=>
    if hI:Supported (C*I) then if hJ:Supported (D*J) then
      (if IsCoprime I J then idealCorrelation (C*I) (D*J) hI hJ z else 0)*
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F z I J
      else 0 else 0
  have he (T:Finset (Ideal O)):
      sectorFrequency η t T β C D hC hD F z=
        ∑I∈sectorPool C hC.1 T,∑J∈sectorPool D hD.1 T,f I J:=by
    calc
      _=∑I:sectorPool C hC.1 T,∑J:sectorPool D hD.1 T,f I J:=by
        unfold sectorFrequency
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro J hJ
        have hc:Supported (C*I):=(supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 T I⟩
        have hd:Supported (D*J):=(supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 T J⟩
        simp only [f,dif_pos hc,dif_pos hd]
      _=_:=by
        simp_rw [Finset.sum_coe_sort]
        exact Finset.sum_coe_sort (sectorPool C hC.1 T)
          (fun I=>∑J∈sectorPool D hD.1 T,f I J)
  rw [he S,he (activeSource S β)]
  symm
  apply sector_pair_sum_active C D hC.1 hD.1 S β f
  · intro I J h
    simp only [f,h,zero_mul,mul_zero]
    split_ifs <;> rfl
  · intro I J h
    simp only [f,h,zero_mul,star_zero,mul_zero]
    split_ifs <;> rfl

 theorem physicalBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun j I J=>physicalKernel C D W K R j I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)*
        dyadicWeight (n 1) (normValue z)*dyadicWeight (n 2) (I.absNorm:ℝ)*
        dyadicWeight (n 3) (J.absNorm:ℝ):ℝ):ℂ)) _

end SevenEighths.CenteredMomentSecondActivePhysicalDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptionalScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSourceBlockWindows
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

lemma scalar_cancel (K G V U c d x y h q M:ℝ)
    (hc:0<c)(hd:0<d)(hx:0<x)(hy:0<y)(hU:0<U)(hq:0≤q) :
    (K/(Real.sqrt c*Real.sqrt d*Real.sqrt x*Real.sqrt y))*(G/U)/Real.sqrt (c*d)*
      (M*U*V*h)/(1+q)=M*((K*G*V/(c*d))*h/(x*y))/(1+q)*Real.sqrt (x*y) := by
  rw [Real.sqrt_mul hc.le,Real.sqrt_mul hx.le]
  have hc':Real.sqrt c≠0:=(Real.sqrt_pos.mpr hc).ne'
  have hd':Real.sqrt d≠0:=(Real.sqrt_pos.mpr hd).ne'
  have hx':Real.sqrt x≠0:=(Real.sqrt_pos.mpr hx).ne'
  have hy':Real.sqrt y≠0:=(Real.sqrt_pos.mpr hy).ne'
  have hq':1+q≠0:=by positivity
  field_simp
  ; ring_nf
  ; simp [Real.sq_sqrt,hc.le,hd.le,hx.le,hy.le]

theorem physical_effective_scale (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K<
      dyadicScale (n 0) := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    have h0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1
    exact (dyadicWeight_support (n 0) h0).2
  · exact False.elim (hz rfl)

theorem actual_residual_sqrt_cap (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))≤
      4*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  have hH:0≤Hsource:=(Nat.cast_nonneg ((C*(I:Ideal O)).absNorm)).trans (hsource _ hI)
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hx:dyadicScale (n 2)≤4*Hsource/(C.absNorm:ℝ):=
    (residual_window_bounds C I hC.1 0 Hsource (n 2) (Nat.cast_nonneg _) (hsource _ hI) hwi).2
  have hy:dyadicScale (n 3)≤4*Hsource/(D.absNorm:ℝ):=
    (residual_window_bounds D J hD.1 0 Hsource (n 3) (Nat.cast_nonneg _) (hsource _ hJ) hwj).2
  have hh:=Real.sqrt_le_sqrt (mul_le_mul hx hy (dyadicScale_pos _).le (by positivity))
  have he:(4*Hsource/(C.absNorm:ℝ))*(4*Hsource/(D.absNorm:ℝ))=
      (4*Hsource)^2/((C.absNorm:ℝ)*D.absNorm):=by ring
  rw [he,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity)] at hh
  exact hh

end SevenEighths.CenteredMomentSecondNonexceptionalScalar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRetainedRatioScalar
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRatioScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSourceBlockWindows
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

open CenteredMomentSecondNonexceptionalScalar

theorem ratio_penalty_le (r a:ℝ) (hr:0< r) (_ha:0≤a) (ha1:a≤1) :
    r/(1+r)*(max 1 (1/r))^a≤1 := by
  by_cases h:r≤1
  · have hi:1≤1/r:=(le_div_iff₀ hr).mpr (by linarith)
    rw [max_eq_right hi]
    have hp: (1/r)^a≤1/r:=Real.rpow_le_self_of_one_le hi ha1
    calc
      _≤ r/(1+r)*(1/r):=mul_le_mul_of_nonneg_left hp (by positivity)
      _=1/(1+r):=by field_simp
      _≤1:=(div_le_one (by positivity)).mpr (by linarith)
  · have hi:1/r≤1:=(div_le_one hr).mpr (by linarith)
    rw [max_eq_left hi,Real.one_rpow,mul_one]
    exact (div_le_one (by positivity)).mpr (by linarith)

theorem actual_envelope_scalar_ratio (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(_hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (a:ℝ)(ha:0≤a)(ha1:a≤1) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
      (max 1 (1/retainedRatio n))^a≤
    (fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hu:0<((∏P∈U,P.val).absNorm:ℝ):=by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  have hn (i:Fin 4):0<dyadicScale (n i):=dyadicScale_pos _
  let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hr:0< r:=div_pos (mul_pos (hn 0) (hn 1)) (mul_pos (hn 2) (hn 3))
  have hscale := (physical_effective_scale η t S β C D hC hD U R rows W K n hne).le
  have he : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((C.absNorm:ℝ)*D.absNorm) := by
    rw [secondEffectiveScale,←normValue_eq_embedding,normValue_mul]
    dsimp only [normValue]
    ring
  have hrat : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))≤ r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale (dyadicScale_pos _).le) (mul_pos (hn 2) (hn 3)).le
  have hfrac : (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)*
        (max 1 (1/r))^a≤1 := by
    apply le_trans _ (ratio_penalty_le r a hr ha ha1)
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hrat (by positivity)) (Real.rpow_nonneg (by positivity) _)
  rw [outerScalar,normalizer,actual_partitionNormalizer C D hC]
  change _≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))
  rw [childEnvelope,scalar_cancel _ _ _ _ _ _ _ _ _ r _ hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) hu hr.le]
  rw [←he]
  calc
    _=((fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      ((secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
        dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)*(max 1 (1/r))^a):=by
      dsimp only [retainedRatio,r];ring
    _≤_:=by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) by positivity)

theorem actual_source_envelope_scalar_ratio (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (a:ℝ)(ha:0≤a)(ha1:a≤1) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
      (max 1 (1/retainedRatio n))^a≤
    4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  apply (actual_envelope_scalar_ratio η t S β C D hC hD U R rows W K hK n hne a ha ha1).trans
  have hh:=mul_le_mul_of_nonneg_left
    (actual_residual_sqrt_cap η t S β C D hC hD U R rows W K n Hsource hsource hne)
    (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm by positivity)
  convert (preTransparency := .instances) hh using 1 ; ring

end SevenEighths.CenteredMomentSecondRetainedRatioScalar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondFrozenRatioCost
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenRatioCost
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentSecondOriginalChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWholeKernel
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedRatioScalar

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondFrozenRatioCost.instDecidableEqSumFinOfNatNat_definitions
theorem actual_canonical_child_ratio_cost (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃Ck:ℝ,0<Ck ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let _r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → 0≤ sourceRadius s → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=CenteredMomentSecondFrozenChosen.actual_canonical_children lo hi W 1 J₁ J₂ B δ hB hδ
  have hfixed:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  refine ⟨4*(fixedFactor:ℝ)*(C0*Ce),by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH0 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hp:=profileCost_nonneg s
  have hhgt:=heightEnvelope_pos s.t
  have hpm1:=profileMoment_nonneg J₁
  have hpm2:=profileMoment_nonneg J₂
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    positivity
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤ sourceRadius s:=
    fun I hi=>(original_column_norm s R0 seed I hz1 hz2 hi).2
  let E:=childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)
  have hdyad:0<dyadicScale (n 1):=dyadicScale_pos _
  have hE:0≤E:=by unfold E childEnvelope;positivity
  have hl:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₁*E)*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b hlive a ha
    simpa only [E,mul_assoc] using hleft L hL hLN hsf χ v b hlive a ha
  have hr:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₂*E)*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b hlive a ha
    simpa only [E,mul_assoc] using hright L hL hLN hsf χ v b hlive a ha
  have hh:=hZ.2 Kphys hKphys n s τ hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 (E₁*E) (E₂*E) (mul_nonneg hE₁ hE) (mul_nonneg hE₂ hE) hl hr
  have hsqrt:Real.sqrt ((E₁*E)*(E₂*E))=E*Real.sqrt (E₁*E₂):=by
    rw [show (E₁*E)*(E₂*E)=E^2*(E₁*E₂) by ring,
      Real.sqrt_mul (sq_nonneg E),Real.sqrt_sq hE]
  simp only [pow_one,hsqrt] at hh
  have hscalar:=actual_source_envelope_scalar_ratio s.η s.t S β C D hC hD U R rows W Kphys hKphys n
    (sourceRadius s) hβ hzero ((1:ℝ)/6) (by norm_num) (by norm_num)
  let F:ℝ:=(C0*Ce)*Z^(2*δ)*profileCost s*Real.sqrt (E₁*E₂)*
    heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by dsimp only [F];positivity
  have hsc:=mul_le_mul_of_nonneg_left hscalar hF
  apply hh.trans
  convert (preTransparency := .instances) hsc using 1 <;> dsimp only [F,E] <;> ring

end SevenEighths.CenteredMomentSecondFrozenRatioCost

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondBlockHarmonicMass
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondBlockHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate CenteredMomentSourceMass
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
local notation "O" => ActualEisensteinCubic.O

lemma pairWeight_nonneg (C D : Ideal O) : 0≤pairWeight C D := by
  unfold pairWeight
  positivity

end SevenEighths.CenteredMomentSecondBlockHarmonicMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondFrozenLiveSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open SevenEighths.CenteredMomentSecondNonexceptionalScalar

namespace SevenEighths.CenteredMomentSecondFrozenLiveSource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondFrozenLiveSource.instDecidableEqSumFinOfNatNat_definitions
theorem original_nonexceptional_energy (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (B L Cr δ ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hδ:0<δ)(hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀s:Input ι,(∀i,s.lo i=lo i)→(∀i,s.hi i=hi i)→
      s.W₁ 0=0→s.W₂ 0=0→0≤ sourceRadius s→sourceRadius s≤Z^B→
    ∀R0 seed:Ideal O,Squarefree seed→seed≠0→
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀(χ₀:RayCharacter)(Q:Ideal O)(m:O),Q≤Ideal.span {(72:O)}→
      m≠0→ goodLambda∣m→(2:O)∣m→
    ∀Kphys Tsec ξ:ℝ,0<Kphys→frequencyRadius Tsec Z ξ≤Cr*Z^L→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      C*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ) := by
  obtain ⟨Ck,hCk,hblock⟩:=actual_canonical_child_ratio_cost lo hi W J₁ J₂ B δ hB hδ
  obtain ⟨Cm,hCm,hmass⟩:=source_part_harmonic_bound B L Cr ε hB hL hCr hε
  refine ⟨Ck*Cm,mul_pos hCk hCm,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s hlo hhi hz1 hz2 hH0 hH R0 seed hseed hseed0 S β
  have hg (q:ActiveLabel S β):=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
  have hs (q:ActiveLabel S β):=commonLabels_supported (activeSource S β) _ _ q.property
  choose τ hf using fun (q:ActiveLabel S β) (U:Finset (CommonIndex q.val.1 q.val.2))=>
    exists_exceptional_family s.η q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.1 U
  refine ⟨τ,hf,?_⟩
  intro χ₀ Q m hQ hm hml hm2 Kphys Tsec ξ hKphys hR E₁ E₂ hE₁ hE₂ hleft hright
  let F:=Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
    Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by
    have hp:=profileCost_nonneg s
    have ht:=heightEnvelope_pos s.t
    have hm1:=profileMoment_nonneg J₁
    have hm2:=profileMoment_nonneg J₂
    have hz:0<Z:=zero_lt_one.trans hZ.1
    dsimp only [F]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hH)
    false s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) (volume s.toData) F
    hKphys hR hH (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))‖/volume s.toData≤F*pairWeight q.val.1 q.val.2:=by
    intro q hq U n
    by_cases hzero:physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))=0
    · rw [hzero,norm_zero,zero_div]
      exact mul_nonneg hF (pairWeight_nonneg _ _)
    · have hh:=hZ.2 Kphys hKphys (fun i=>(n i:ℤ)) s (τ q U) hlo hhi R0 seed
        q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.2.1 (hg q).2.2.2.2.1
        ((hg q).2.2.2.2.2.1.trans hH) ((hg q).2.2.2.2.2.2.trans hH) (hg q).2.2.1 U (hf q U)
        hz1 hz2 hH0 hH (frequencyRadius Tsec Z ξ) Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂
        (hleft q hq U n hzero) (hright q hq U n hzero)
      rw [←physicalBlock_active]
      exact hh.trans_eq (by dsimp only [F,pairWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*δ)*Z^ε=Z^(2*δ+ε):=by rw [Real.rpow_add (zero_lt_one.trans hZ.1)]
  dsimp only [F]
  calc
    _=(Ck*Cm)*(Z^(2*δ)*Z^ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]
end SevenEighths.CenteredMomentSecondFrozenLiveSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondFrozenLiveDescent
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open SevenEighths.CenteredMomentSecondNonexceptionalScalar

namespace SevenEighths.CenteredMomentSecondFrozenLiveDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondFrozenLiveDescent.instDecidableEqSumFinOfNatNat_definitions
theorem original_source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i,hi i)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving) :=by
  obtain ⟨Cmain,hCmain,hmain⟩:=
    CenteredMomentSecondFrozenLiveSource.original_nonexceptional_energy lo hi W J₁ J₂
      B B 1 δ ε hB hB zero_lt_one hδ hε
  obtain ⟨J,Sprofile,SΦ,hSp,Cexc,Cdiag,Ctail,hCexc,hCdiag,hCtail,hrem⟩:=
    CenteredMomentSecondSourceRemainder.original_source_remainder wlo whi hwlo hwhi
      lo hi hhi W ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sprofile,SΦ,hSp,Cmain,Cexc,Cdiag,Ctail,hCmain,hCexc,hCdiag,hCtail,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hrem⟩:=hrem Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hmain,hrem] with Z hmZ hrZ
  refine ⟨hmZ.1,?_⟩
  intro s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (p.support i hn).1
  have hz1:s.W₁ 0=0:=by rw [hw1];exact hz 0
  have hz2:s.W₂ 0=0:=by rw [hw2];exact hz 1
  obtain ⟨τ,hfamily,hchild⟩:=hmZ.2 s hlo hhis hz1 hz2 hH0 hH R0 seed hseed hseed0
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂
    hleft hright r hX1 hX2 hY1 hY2
  have hn:=hchild χ₀ Q m hQ72 hm hml hm2 Kphys Tsec ξ hKphys
    (by simpa only [one_mul] using hRcap) E₁ E₂ hE₁ hE₂ hleft hright
  have he:=hrZ.2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
    χ₀ m hm hml hm2 Tsec Kphys hKphys hVcap hTcap hnom hR hRcap r hX1 hX2 hY1 hY2
  have ht:‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData+
      ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData:=by
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (volume_pos s.toData).le
    have h:=norm_add_le
      (partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
      (sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
    simpa only [←add_sub_assoc, add_sub_cancel_left] using h
  exact ht.trans ((add_le_add hn he).trans_eq (by ring))

end SevenEighths.CenteredMomentSecondFrozenLiveDescent

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondUniformSubsetSource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

local instance instDecidableEqSumFinOfNatNat_solutions_r607a1b_1 : DecidableEq (ι⊕Fin 2):=Classical.decEq _
lemma control_mono {wlo whi : ℝ} (p : Profiles wlo whi)
    {S T : Finset (ℕ×ℕ)} (h : S⊆T) : p.control S≤p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma moment_mono {j k : ℕ} (h : j≤k) : profileMoment j≤profileMoment k := by
  apply integral_mono (columnDensity_moments _ logAnnulus_compact logAnnulus_smooth j)
    (columnDensity_moments _ logAnnulus_compact logAnnulus_smooth k)
  intro x
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg x]) h) (norm_nonneg _)

omit [DecidableEq ι] in
lemma factor_mono {wlo whi : ℝ} {S T : Finset (ℕ×ℕ)} (hST : S⊆T)
    (s : Input ι) (p : Profiles wlo whi) {j k : ℕ} (hjk : j≤k)
    (Q : Ideal O) {A B : ℝ} (hA : 0≤A) (hAB : A≤B) :
    profileFactor S s p j Q A≤profileFactor T s p k Q B := by
  have hp:=control_mono p hST
  have hpn:=p.control_nonneg S
  have hpn':=p.control_nonneg T
  have hm:=moment_mono hjk
  have hmn:=profileMoment_nonneg j
  have hmn':=profileMoment_nonneg k
  have hπ : (1:ℝ)≤1+2*Real.pi := by linarith [Real.pi_pos]
  have ht : (1:ℝ)≤1+‖s.t‖ := by linarith [norm_nonneg s.t]
  have h4 : 4*j≤4*k := Nat.mul_le_mul_left _ hjk
  have h2 : 2*j≤2*k := Nat.mul_le_mul_left _ hjk
  have hπpow:=pow_le_pow_right₀ hπ h4
  have htpow:=pow_le_pow_right₀ ht h2
  have hB : 0≤B := hA.trans hAB
  unfold profileFactor
  change A*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*j)*
    p.control S^2*(1+‖s.t‖)^(2*j)*slotControl s.toData^2*frozenProfile s^2*profileMoment j^2 ≤ _
  change _ ≤ B*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*k)*
    p.control T^2*(1+‖s.t‖)^(2*k)*slotControl s.toData^2*frozenProfile s^2*profileMoment k^2
  gcongr

open CenteredMomentSourceInputReindex CenteredMomentAmplificationChildInput CenteredMomentCommonProfile

end SevenEighths.CenteredMomentSecondUniformSubsetSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstNestedSeededGaussianPower
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNestedSeededGaussianPower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

open CenteredMomentAmplificationChildInput
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstSeededGaussianPower CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondUniformSubsetSource

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstNestedSeededGaussianPower.instDecidableEqSumFinOfNatNat_definitions
theorem nested_source_descent_oai (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i:T.2,hi i.val.val)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving)  := by
  have hall (T : NestedIndex ι) := CenteredMomentSecondFrozenLiveDescent.original_source_descent
    wlo whi hwlo hwhi (fun i:T.2=>lo i.val.val) (fun i:T.2=>hi i.val.val) (fun i=>hhi i.val.val)
    W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  choose J Sp Sf hSp Cm Ce Cd Ct hCm hCe hCd hCt hbound using hall
  let J0 : ℕ := ∑T:NestedIndex ι,J T
  let Sp0 := Finset.univ.biUnion Sp
  let Sf0 := Finset.univ.biUnion Sf
  let Cm0 : ℝ := 1+∑T:NestedIndex ι,Cm T
  let Ce0 : ℝ := 1+∑T:NestedIndex ι,Ce T
  let Cd0 : ℝ := 1+∑T:NestedIndex ι,Cd T
  let Ct0 : ℝ := 1+∑T:NestedIndex ι,Ct T
  have sum_pos (f : NestedIndex ι→ℝ) (hf : ∀T,0≤f T) : 0<1+∑T:NestedIndex ι,f T := by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (NestedIndex ι)))=>hf T)
    linarith
  have sum_le (f : NestedIndex ι→ℝ) (hf : ∀T,0≤f T) (T : NestedIndex ι) : f T≤1+∑U:NestedIndex ι,f U := by
    have hh:=Finset.single_le_sum (fun U (_:U∈(Finset.univ:Finset (NestedIndex ι)))=>hf U) (Finset.mem_univ T)
    linarith
  refine ⟨J0,Sp0,Sf0,Finset.mem_biUnion.mpr ⟨emptyIndex,Finset.mem_univ _,hSp emptyIndex⟩,
    Cm0,Ce0,Cd0,Ct0,sum_pos Cm (fun T=>(hCm T).le),(sum_pos Ce hCe).le,
    sum_pos Cd (fun T=>(hCd T).le),sum_pos Ct (fun T=>(hCt T).le),?_⟩
  intro Q hQ hQt hQ72
  choose K hK hev using fun T=>hbound T Q hQ hQt hQ72
  let K0 : ℝ := 1+∑T:NestedIndex ι,K T
  refine ⟨K0,sum_pos K (fun T=>(hK T).le),?_⟩
  have heall : ∀ᶠ Z : ℝ in atTop, ∀T:NestedIndex ι,_ := Filter.eventually_all.mpr hev
  filter_upwards [heall] with Z hZ
  refine ⟨(hZ emptyIndex).1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=(hZ T).2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hsp : Sp T⊆Sp0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hsf : Sf T⊆Sf0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hj : J T≤J0 := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hcm:=sum_le Cm (fun T=>(hCm T).le) T
  have hce:=sum_le Ce hCe T
  have hcd:=sum_le Cd (fun T=>(hCd T).le) T
  have hct:=sum_le Ct (fun T=>(hCt T).le) T
  have hfactor:=factor_mono hsp s p hj Q (hK T).le (sum_le K (fun T=>(hK T).le) T)
  have hfn:=profileFactor_nonneg (Sp T) s p (J T) Q (K T) (hK T).le
  have hphi : (Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤Sf0.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := Seminorm.le_def.mp (Finset.sup_mono hsf) W
  have hz : 0≤Z := (hZ T).1.le.trans' zero_le_one
  have hp:=profileCost_nonneg s
  have hm1:=profileMoment_nonneg J₁
  have hm2:=profileMoment_nonneg J₂
  have he:=heightEnvelope_pos s.t
  have hsn : 0≤(seed.absNorm:ℝ) := by positivity
  have hvol:=CenteredMomentSourceInputTailUniform.volume_pos s
  have hc : 0≤(Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  have hCm0 : 0≤Cm0 := (sum_pos Cm (fun T=>(hCm T).le)).le
  have hCe0 : 0≤Ce0 := (sum_pos Ce hCe).le
  have hCd0 : 0≤Cd0 := (sum_pos Cd (fun T=>(hCd T).le)).le
  have hCt0 : 0≤Ct0 := (sum_pos Ct (fun T=>(hCt T).le)).le
  have hprodhi : 0≤∏i:T.2,hi i.val.val := Finset.prod_nonneg (fun i _=>hhi i.val.val)
  have hprodlo : 0≤∏i:T.2,s.lo i := Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentFirstNestedSeededGaussianPower

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentFirstNestedSeededGaussianPower.nested_source_descent_oai.{u_1} := @OAI.SevenEighths.CenteredMomentFirstNestedSeededGaussianPower.nested_source_descent_oai.{u_1}
