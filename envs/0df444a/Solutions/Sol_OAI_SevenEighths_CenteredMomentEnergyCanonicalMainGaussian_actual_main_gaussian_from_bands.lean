-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyCanonicalMainGaussian.actual_main_gaussian_from_bands
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:48:01.626993+00:00
-- url     : https://prove2.me/submissions/89364246-812b-4803-a75e-1b520426f458

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalMainUniform_actual_main_uniform_child
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondFrozenUniformSubset_original_subsets_source_descent

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
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
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorAmplitude
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorAmplitude
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentDetectorDictionary
open ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma slotControl_nonneg (s:Data ι):0≤ slotControl s:=by
  unfold slotControl
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>(zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _)))

end SevenEighths.CenteredMomentAllocatedDetectorAmplitude

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dirichlet
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

variable [NeZero q]

end SevenEighths.HeckeDirichlet

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplificationChildSourceCaps
open ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEq_solutions_rb4fa1c_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
theorem radius_le (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 0≤b₁) (_h₂ : 0≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤ s.hi i) (hhib : ∀i,s.hi i≤b)
    (hs₁ : 0≤ s.b₁) (hs₂ : 0≤ s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧ CenteredMomentOriginalCommonHarmonic.sourceRadius s≤(b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s := by
  have hp:0≤∏i,s.hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hp':(∏i,s.hi i)≤b^N := by
    calc
      _ ≤ ∏i:ι,b := Finset.prod_le_prod (fun i _=>hhi i) (fun i _=>hhib i)
      _ = b^Fintype.card ι := by simp
      _ ≤ b^N := pow_le_pow_right₀ hb hc
  have hpp:=mul_le_mul (mul_le_mul hp' hb₁ hs₁ (pow_nonneg (zero_le_one.trans hb) _)) hb₂ hs₂
    (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) h₁)
  change 0≤_ ∧ _≤_
  have he:CenteredMomentOriginalCommonHarmonic.sourceRadius s=((∏i,s.hi i)*s.b₁*s.b₂)*CenteredMomentAmplificationChildInput.volume s := by
    unfold CenteredMomentOriginalCommonHarmonic.sourceRadius CenteredMomentAmplificationChildInput.volume; ring
  rw [he]
  exact ⟨mul_nonneg (mul_nonneg (mul_nonneg hp hs₁) hs₂)
    (CenteredMomentAmplificationChildInput.volume_pos s).le,
    mul_le_mul_of_nonneg_right hpp (CenteredMomentAmplificationChildInput.volume_pos s).le⟩

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCost
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalCost
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma frozenProfile_nonneg (s:Input ι):0≤frozenProfile s:=by
  unfold frozenProfile
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

end SevenEighths.CenteredMomentCommonExceptionalCost

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceLowerSupport
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma tuple_norm_product {ι:Type*} [Fintype ι] (v:Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct v):ℝ)=
      (∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ))*
      (Ideal.absNorm (v (Sum.inr 0)):ℝ)*(Ideal.absNorm (v (Sum.inr 1)):ℝ) := by
  simp only [finiteTupleProduct,map_prod,Nat.cast_prod,map_mul,Nat.cast_mul,Fintype.prod_sum_type,Fin.prod_univ_two]
  ring

 theorem profile_product_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0<P i) (ha:∀i,0≤a i) (ha₁:0≤a₁) (ha₂:0≤a₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤x)
    (hs₁:∀x,W₁ x≠0→a₁≤x) (hs₂:∀x,W₂ x≠0→a₂≤x)
    (v:Tuple ι) (hv:profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm (finiteTupleProduct v):ℝ) := by
  have hslot:∀i,Wslot i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/P i)≠0:=by
    intro i
    have hp: (∏j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))≠0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact (mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _))).2
  have hrect:idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))≠0:=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  have hslots:(∏i,a i)*(∏i,P i)≤∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ):=by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _=>mul_nonneg (ha i) (hP i).le)
    intro i hi
    exact (le_div_iff₀ (hP i)).mp (hs i _ (hslot i))
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hplain:a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
      ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
    have hbranch (X Y:ℝ) (hX:0<X) (hY:0<Y) (hXY:X*Y=T)
        (hn:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X)*
          W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y)≠0) :
        a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
          ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
      have h1: a₁*X≤(Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ):=
        (le_div_iff₀ hX).mp (hs₁ _ (mul_ne_zero_iff.mp hn).1)
      have h2: a₂*Y≤(Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ):=
        (le_div_iff₀ hY).mp (hs₂ _ (mul_ne_zero_iff.mp hn).2)
      have hh:=mul_le_mul h1 h2 (mul_nonneg ha₂ hY.le) (Nat.cast_nonneg _)
      simp only [map_mul,Nat.cast_mul] at hh
      rw [←hXY]
      nlinarith
    unfold idealRectangle at hrect
    by_cases hx:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂)=0
    · have hy:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/Y₁)*
        W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y₂)≠0:=by
        intro hy
        exact hrect (by rw [hx,hy,sub_self])
      exact hbranch Y₁ Y₂ hY₁ hY₂ hYT hy
    · exact hbranch X₁ X₂ hX₁ hX₂ hXT hx
  have hT:0<T:=hXT ▸ mul_pos hX₁ hX₂
  have hp:=mul_le_mul hslots hplain (mul_nonneg (mul_nonneg ha₁ ha₂) hT.le)
    (Finset.prod_nonneg (fun _ _=>Nat.cast_nonneg _))
  rw [tuple_norm_product]
  have he:(∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)=
      ((∏i,a i)*(∏i,P i)*(a₁*a₂*T))/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))).mpr
  convert (preTransparency := .instances) hp using 1 ; ring

 theorem profile_column_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0<P i) (ha:∀i,0≤a i) (ha₁:0≤a₁) (ha₂:0≤a₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤x)
    (hs₁:∀x,W₁ x≠0→a₁≤x) (hs₂:∀x,W₂ x≠0→a₂≤x)
    (S:Finset (Tuple ι)) (I:Ideal O)
    (hI:finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm I:ℝ) := by
  obtain ⟨v,hv,hv0,he⟩:=CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness S
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I hI
  have hh:=profile_product_lower R ν Wslot P a W₁ W₂ a₁ a₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP ha ha₁ ha₂ hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hXT hYT hs hs₁ hs₂ v hv0
  simpa only [he] using hh

end SevenEighths.CenteredMomentSourceLowerSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSourceSupport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceLowerSupport CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstPhysicalSourceSupport.instDecidableEqSumFinOfNatNat_definitions
theorem original_column_lower {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(a₁ a₂:ℝ)(ha₁:0≤a₁)(ha₂:0≤a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hn:CenteredMomentOriginalCommonHarmonic.coefficient s R seed I≠0):
    (∏i,s.lo i)*a₁*a₂*volume s.toData≤(I.absNorm:ℝ) := by
  have hh:=profile_column_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos
    (fun i=>(s.lo_pos i).le) ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product (fun i x hx=>(s.support i hx).1)
    hs₁ hs₂ (Fintype.piFinset s.pools) I (by
      simpa only [CenteredMomentOriginalCommonHarmonic.coefficient] using hn)
  simpa only [map_one,Nat.cast_one,mul_one,div_one,volume,mul_assoc] using hh

end SevenEighths.CenteredMomentFirstPhysicalSourceSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyChildEnvelopeFitting
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentSecondNonexceptionalChosenBlock
local notation "O" => HeckeFamily.O

lemma coefficient_nonneg {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ)(hC:0≤Cc)(h₀:0≤C₀)(h₁:0≤C₁)
    (hH:0≤height)(hZ:0≤Z):0≤ coefficient Cc C₀ C₁ p T height degree Z exponent:=by
  unfold coefficient
  have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile
  positivity

end SevenEighths.CenteredMomentEnergyChildEnvelopeFitting

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤ mass s :=
  Finset.one_le_prod (fun i _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤ mass s := zero_le_one.trans (mass_one s)

omit [DecidableEq ι] in
lemma child_mass (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : mass (child s C R B τ t)≤ mass s := by
  change (∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma child_card (B : CenteredMomentAddedZeroUniform.Tuple ι) :
    Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa using Finset.card_le_card (Finset.subset_univ (liveIndices B))

omit [DecidableEq ι] in
lemma slot_control_bound (s : Input ι) (b : ℝ) (hb : 1≤b) (hu : s.upper≤b) :
    slotControl s.toData≤(128*b)^Fintype.card ι*mass s^2 := by
  have hpoint (i : ι) : max 1 (128*max 0 (s.hi i)*s.M i)≤(128*b)*s.M i := by
    apply max_le
    · have hM:=s.M_ge_one i
      nlinarith
    · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (s.M_ge_one i))
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) ((s.upper_ge i).trans hu)) (by norm_num)
  have hp:=Finset.prod_le_prod (fun i (_:i∈Finset.univ)=>by positivity)
    (fun i (_:i∈Finset.univ)=>hpoint i)
  calc
    slotControl s.toData=mass s*(∏i,max 1 (128*max 0 (s.hi i)*s.M i)):=rfl
    _≤ mass s*(∏i,(128*b)*s.M i):=mul_le_mul_of_nonneg_left hp (mass_nonneg s)
    _=(128*b)^Fintype.card ι*mass s^2:=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      unfold mass
      ring

omit [DecidableEq ι] in
lemma profile_cost_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileCost s≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*A^2)*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have hm2:=pow_le_pow_left₀ (mass_nonneg s) hm 2
  have h:=mul_le_mul hm2 hp (by positivity) (sq_nonneg A)
  have h':=(mul_le_mul_of_nonneg_right h
    (show 0≤2*(max 1 s.b₁*max 1 s.b₂)*mass s^2 by positivity))
  convert (preTransparency := .instances) h' using 1 <;> simp only [profileCost,Data.profileFactor,mass]; ring

omit [DecidableEq ι] in
lemma exceptional_slot_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    slotControl s.toData^2*frozenProfile s^2≤
      ((128*b)^N)^2*(b^N)^2*A^4*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have h128 : (1:ℝ)≤128*b := by linarith
  have hs : slotControl s.toData≤(128*b)^N*mass s^2 :=
    (slot_control_bound s b hb hu).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h128 hc) (sq_nonneg _))
  have hf : frozenProfile s≤ mass s*b^N :=
    mul_le_mul_of_nonneg_left hp (mass_nonneg s)
  have h:=mul_le_mul (pow_le_pow_left₀ (slotControl_nonneg _) hs 2)
    (pow_le_pow_left₀ (frozenProfile_nonneg s) hf 2) (sq_nonneg _) (sq_nonneg _)
  calc
    _≤((128*b)^N*mass s^2)^2*(mass s*b^N)^2:=h
    _=((128*b)^N)^2*(b^N)^2*mass s^4*mass s^2:=by ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg s) hm 4) (by positivity))
      (sq_nonneg _)

omit [DecidableEq ι] in
lemma exceptional_factor_bound {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K : ℝ)
    (hK : 0≤K) (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileFactor S s p J Q K≤exceptionalConstant N b J Q K*
      p.control S^2*(1+‖s.t‖)^(2*J)*A^4*mass s^2 := by
  have h:=exceptional_slot_bound s N b A hb hu hc hm
  let F:=K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*p.control S^2*(1+‖s.t‖)^(2*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hh:=mul_le_mul_of_nonneg_left h hF
  convert (preTransparency := .instances) hh using 1 <;> simp only [profileFactor,exceptionalConstant,F] <;> ring

end SevenEighths.CenteredMomentFirstChildProfileControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondChildPowerBudget
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentFirstChildProfileControl CenteredMomentCommonRadialPointwise
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma endpoint_product (s : Input ι) (N : ℕ) (b : ℝ) (hb : 1≤b)
    (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤ s.hi i) :
    0≤∏i,s.hi i ∧ (∏i,s.hi i)≤b^N := by
  refine ⟨Finset.prod_nonneg (fun i _=>hhi i),?_⟩
  calc
    _≤∏i:ι,b:=Finset.prod_le_prod (fun i _=>hhi i) (fun i _=>(s.upper_ge i).trans hu)
    _=b^Fintype.card ι:=by simp
    _≤b^N:=pow_le_pow_right₀ hb hc

omit [DecidableEq ι] in
lemma main_cost (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤ s.hi i)
    (hs₁ : 0≤ s.b₁) (hs₂ : 0≤ s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) :
    profileCost s*sourceRadius s≤
      (2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)*
        CenteredMomentAmplificationChildInput.volume s*mass s^2 := by
  have hg:=CenteredMomentAmplificationChildSourceCaps.radius_le N b b₁ b₂ hb
    (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc hhi
    (fun i=>(s.upper_ge i).trans hu) hs₁ hs₂ hb₁ hb₂
  have hp:=profile_cost_bound s N b A hb hu hc hm
  have he : max 1 s.b₁*max 1 s.b₂≤b₁*b₂ :=
    mul_le_mul (max_le h₁ hb₁) (max_le h₂ hb₂) (by positivity) (by linarith)
  have hp' : profileCost s≤(2*(b₁*b₂)*b^N*A^2)*mass s^2 := by
    apply hp.trans
    gcongr
  have hh:=mul_le_mul hp' hg.2 hg.1 (by positivity)
  convert (preTransparency := .instances) hh using 1 ; ring

omit [DecidableEq ι] in
lemma diagonal_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) (N : ℕ) (b whi ε : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (hhi : ∀i,0≤ s.hi i) (hε : 0≤ε) :
    (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)≤
    (4*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
      (1+b^N*whi^2)^(1+ε))*mass s^2 := by
  have hp:=endpoint_product s N b hb hu hc hhi
  have hx : 1+(∏i,s.hi i)*whi*whi≤1+b^N*whi^2 := by nlinarith [mul_le_mul_of_nonneg_right hp.2 (sq_nonneg whi)]
  have hx0 : 0≤1+(∏i,s.hi i)*whi*whi := by nlinarith [mul_nonneg hp.1 (sq_nonneg whi)]
  have h:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx (by linarith : 0≤1+ε))
    (sq_nonneg (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s))
  convert (preTransparency := .instances) h using 1 ; ring

omit [DecidableEq ι] in
lemma tail_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) :
    plainControl s W₁ W₂^2=
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*mass s^2 := by
  unfold plainControl mass
  ring

omit [DecidableEq ι] in
theorem source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤ s.hi i)
    (hs₁ : 0≤ s.b₁) (hs₂ : 0≤ s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ) (hK : 0≤K) (hε : 0≤ε)
    (hs : 0≤ seedNorm) (a : Fin 4→ℝ) (ha : ∀j,0≤a j) :
    sourceCost s S p J Q K ε seedNorm a ≤
      (∑j,coefficients N b b₁ b₂ A S p J Q K s.t ε seedNorm a j*
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  unfold sourceCost
  have hv := (CenteredMomentAmplificationChildInput.volume_pos s).le
  have hmain:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (main_cost s N b b₁ b₂ A hb h₁ h₂ hu hc hhi hs₁ hs₂ hb₁ hb₂ hm) (ha 0)) hs
  have hexc:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exceptional_factor_bound S p J Q K hK s N b A hb hu hc hm) (ha 1))
      (Real.rpow_nonneg hv (1/3:ℝ))) hs
  have hdiag:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (diagonal_cost s (p.profile 0) (p.profile 1) N b whi ε hb hu hc hhi hε) (ha 2))
      (Real.rpow_nonneg hv ε)) hs
  have htail:=congrArg (fun x:ℝ=>a 3*x) (tail_cost s (p.profile 0) (p.profile 1))
  have hh:=add_le_add (add_le_add (add_le_add hmain hexc) hdiag) (le_of_eq htail)
  convert (preTransparency := .instances) hh using 1 <;>
    (try simp only [coefficients,powers,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,
      Real.rpow_one,Real.rpow_zero]) <;> ring

end SevenEighths.CenteredMomentSecondChildPowerBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSourcePowerDescent
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourcePowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock
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
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

local instance instDecidableEqSumFinOfNatNat_solutions_rb4fa1c_1 : DecidableEq (ι⊕Fin 2):=Classical.decEq _
lemma physicalFactors_nonneg (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ))
    (hm : 0≤Cmain) (he : 0≤Cexc) (hd : 0≤Cdiag) (ht : 0≤Ctail)
    (hZ : 0≤Z) (hK : 0≤K) (hη : 0≤ηNorm) (hl : 0≤loProduct) :
    ∀j,0≤physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
      loProduct wlo J₁ J₂ SΦ W j := by
  have hp1:=profileMoment_nonneg J₁
  have hp2:=profileMoment_nonneg J₂
  have hheight:=(heightEnvelope_pos t).le
  have hlo : 0≤loProduct*wlo*wlo := by nlinarith [mul_nonneg hl (sq_nonneg wlo)]
  have hs : 0≤SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  intro j
  fin_cases j <;> dsimp [physicalFactors] <;> positivity

end SevenEighths.CenteredMomentSecondSourcePowerDescent

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputTailSeed
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailSeed
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_rb4fa1c_2 : DecidableEq (ι⊕Fin 2) := Classical.decEq _
lemma paid_seed_power (Z Bseed saving seedNorm : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) :
    Z^(-(saving+Bseed))≤Z^(-saving)/seedNorm := by
  apply (le_div_iff₀ hs).mpr
  calc
    _≤Z^(-(saving+Bseed))*Z^Bseed :=
      mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg hZ.le _)
    _=Z^(-saving) := by rw [←Real.rpow_add hZ];congr 1;ring

lemma paid_seed_term (Z Bseed saving seedNorm A : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) (hA : 0≤A) :
    A*Z^(-(saving+Bseed))≤A*Z^(-saving)/seedNorm := by
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (paid_seed_power Z Bseed saving seedNorm hZ hs hcap) hA

end SevenEighths.CenteredMomentSourceInputTailSeed

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondFrozenSeededPowerDescent
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock
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
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent.instDecidableEqSumFinOfNatNat_definitions
theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
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
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
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
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondFrozenUniformSubset.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ (saving+Bseed) hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=seededFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ Sf W
  have hapos:=physicalFactors_nonneg Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hseedpos : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed0)
  have ha : ∀j,0≤a j := by
    intro j
    fin_cases j
    · exact hapos 0
    · exact hapos 1
    · exact hapos 2
    · exact div_nonneg (hapos 3) hseedpos.le
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    apply hh.trans
    have htail:=paid_seed_term Z Bseed saving (seed.absNorm:ℝ)
      (Ct*plainControl s (p.profile 0) (p.profile 1)^2*
        Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys)
      (zero_lt_one.trans hZ.1) hseedpos hseedcap (by positivity)
    dsimp [sourceCost,a,seededFactors,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring_nf at htail ⊢
    linarith only [htail]
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondReferenceNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondReferenceNormalization
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSectorLocalization CenteredMomentSecondSourcePowerDescent
open CenteredMomentSecondSourceSeededPowerDescent
local notation "O"=>HeckeFamily.O

lemma envelope_rescale (η:Character)(qref E:ℝ)(C D:Ideal O)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    (qref/(η.modulus.absNorm:ℝ)*E)*childEnvelope η C D U n=
      E*referenceEnvelope qref C D U n:=by
  have hq:(η.modulus.absNorm:ℝ)≠0:=by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot
  unfold childEnvelope referenceEnvelope
  field_simp

lemma paired_rescale (q qref E₁ E₂:ℝ)(hq:0<q)(hr:0≤qref):
    q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂))=qref*Real.sqrt (E₁*E₂):=by
  rw [show (qref/q*E₁)*(qref/q*E₂)=(qref/q)^2*(E₁*E₂) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (div_nonneg hr hq.le)]
  field_simp

lemma physicalFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo J₁ J₂ SΦ W=
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo J₁ J₂ SΦ W:=by
  funext j
  fin_cases j
  · dsimp [physicalFactors]
    have hh:=paired_rescale q qref E₁ E₂ hq hr
    calc
      _=Cmain*Z^(2*δ+ε)*(q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂)))*
        CenteredMomentSecondWindowBudget.heightEnvelope t^(J₁+J₂)*
        CenteredMomentSecondWindowBudget.profileMoment J₁*CenteredMomentSecondWindowBudget.profileMoment J₂:=by ring
      _=_:=by rw [hh];ring
  all_goals rfl

lemma seededFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo seed:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo seed J₁ J₂ SΦ W=
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo seed J₁ J₂ SΦ W:=by
  unfold seededFactors
  rw [physicalFactors_rescale Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W hq hr]

end SevenEighths.CenteredMomentSecondReferenceNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondFrozenReferenceSeededPowerDescent
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock
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
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent.instDecidableEqSumFinOfNatNat_definitions
theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
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
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
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
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
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
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    CenteredMomentSecondFrozenSeededPowerDescent.original_subsets_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hq:0<(s.η.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ s.η.modulus_ne_bot
  have hr:0≤qref/(s.η.modulus.absNorm:ℝ):=div_nonneg hqref.le hq.le
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap
    (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂)
    (mul_nonneg hr hE₁) (mul_nonneg hr hE₂)
  have hbound:=hh
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hleft q hq U n hn D0 hD hcap hs χ v b hb a ha)
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hright q hq U n hn D0 hD hcap hs χ v b hb a ha)
    r hX1 hX2 hY1 hY2
  rw [seededFactors_rescale Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ)
      J₁ J₂ Sf W hq hqref.le] at hbound
  exact hbound

end SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSeededGaussianPower
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSeededGaussianPower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock
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
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

open CenteredMomentAmplificationChildInput
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstSeededGaussianPower.instDecidableEqSumFinOfNatNat_definitions
omit [DecidableEq ι] in
lemma normalized_source_le_norm (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource s R seed W K≤
      ‖sourceGaussEnergy (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) (heightCoeff s.η s.t) W K‖/
          CenteredMomentAmplificationChildInput.volume s := by
  exact div_le_div_of_nonneg_right (Complex.re_le_norm _)
    (CenteredMomentAmplificationChildInput.volume_pos s).le

theorem actual_subsets_seeded_gaussian_power (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
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
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
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
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
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
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    normalizedGaussSource s R0 seed W Kphys≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    CenteredMomentSecondFrozenReferenceSeededPowerDescent.original_subsets_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  exact (normalized_source_le_norm s R0 seed W Kphys).trans
    (hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
      E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2)

end SevenEighths.CenteredMomentFirstSeededGaussianPower

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondInputCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonHeightEnvelope
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.instDecidableEq_definitions
theorem actual_lower_support (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤ s.lower)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R seed I:Ideal O)(hne:coefficient s R seed I≠0):
    lowerFactor N slotLower plainLower*volume s≤(I.absNorm:ℝ):=by
  have hm:0≤ min 1 slotLower:=(lt_min zero_lt_one hs).le
  have hprod:(min 1 slotLower)^N≤∏i,s.lo i:=by
    apply (pow_le_pow_of_le_one hm (min_le_left _ _) hc).trans
    have hh:=Finset.prod_le_prod (s:=Finset.univ) (f:=fun _:ι=>min 1 slotLower)
      (g:=fun i=>s.lo i) (fun _ _=>hm)
      (fun i _=>(min_le_right _ _).trans (hlo.trans (s.lower_le i)))
    simpa only [Finset.prod_const,Finset.card_univ] using hh
  have hh:=original_column_lower s R seed I plainLower plainLower hp.le hp.le hW₁ hW₂ hne
  change (∏i,s.lo i)*plainLower*plainLower*volume s≤(I.absNorm:ℝ) at hh
  apply le_trans _ hh
  have hv:0≤volume s:=(volume_pos s).le
  unfold lowerFactor
  nlinarith [mul_le_mul_of_nonneg_right hprod (mul_nonneg (sq_nonneg plainLower) hv)]

end SevenEighths.CenteredMomentSecondInputCapacitySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalMainGaussian
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainGaussian
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainGaussian.instDecidableEqSumFinOfNatNat_definitions
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalMainGaussian.instFiniteQuotientOIdeal
theorem actual_main_gaussian_from_bands_oai
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤ sigma → 1≤ cost → 0<asource →
    0≤delta → 0≤ reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    (∀q∈liveLabels input.η Scols β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀dyad:SourceBlocks q.val.1 q.val.2 U Kmain (frequencyRadius (nominal input Kmain) Z ξ)
        (sourceRadius input),
      physicalBlock input.η input.t (activeSource Scols β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U
        (frequencyRadius (nominal input Kmain) Z ξ)
        (partRows false input.η χ₀ (internalQ Q η₀) m q.val.1 q.val.2 U
          (frequencyRadius (nominal input Kmain) Z ξ))
        CenteredMomentFirstAmplificationChoice.ballProfile Kmain (fun i=>(dyad i:ℤ))≠0 →
      ∀χ:RayCharacter,Real.logb Z (dyadicScale (dyad 1))+
        Real.logb Z ((family q U χ).modulus.absNorm:ℝ)≤Mcap) →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc t
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kmain t
          (cost*(τ.modulus.absNorm:ℝ)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,hmain⟩:=
    CenteredMomentEnergyCanonicalMainUniform.actual_main_uniform_child (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
      N lower upper a0 Bcap Bcap θsource hlower ha0 hθsource
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hgauss⟩:=
    actual_subsets_seeded_gaussian_power a b haPlain hbPlain lows highs hhighs
      CenteredMomentFirstAmplificationChoice.ballProfile (dc+degree+4*n) (dc+degree+4*n)
      N upper (max 1 b) (max 1 b) hupper (le_max_left _ _) (le_max_left _ _)
      εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Zm,hZm,hm⟩:=hmain η₀
  obtain ⟨Kc,hKc,hevent⟩:=hgauss (internalQ Q η₀) hQ0 hQt hQ72
  obtain ⟨Zg,hZg⟩:=Filter.eventually_atTop.1 hevent
  refine ⟨Kc,hKc,max Zm Zg,lt_of_lt_of_le hZm (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  let input:=child src C R0 B τ t
  let Km:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
  have hZmZ:Zm≤Z:=(le_max_left _ _).trans hZ
  have hgZ:=hZg Z ((le_max_right _ _).trans hZ)
  have hz:1<Z:=hgZ.1
  have hP:∀i,1≤ input.P i:=by
    intro i
    change 1≤ src.P i.val
    rw [hmatch.scale]
    exact Real.one_le_rpow hz.le (hw i.val)
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤N:=
    (child_card B.val).trans hcard
  have hlowerBeta (I:Ideal O)(hne:coefficient input (R0*C) seed I≠0):
      asource*volume input≤(I.absNorm:ℝ):=by
    apply (mul_le_mul_of_nonneg_right hsourceLower (volume_pos input).le).trans
    apply CenteredMomentSecondInputCapacitySource.actual_lower_support N lower a hlower haPlain
      input hcardInput hlowerSrc ?_ ?_ (R0*C) seed I hne
    · intro x hx
      change src.W₁ x≠0 at hx
      rw [←hp₁] at hx
      exact (p.support 0 hx).1
    · intro x hx
      change src.W₂ x≠0 at hx
      rw [←hp₂] at hx
      exact (p.support 1 hx).1
  have hsource:=hgZ.2 (CenteredMomentCommonProfile.liveIndices B.val) input p
    (fun i=>hloSrc i.val) (fun i=>hhiSrc i.val) hP hp₁.symm hp₂.symm (mass src)
    hupperSrc hcardInput hb1 hb2 hb1max hb2max (child_mass src C R0 B τ t)
    (R0*C) seed hready.puncture_ne hseed hseed0 hseedcap hready.source_nonneg hready.source_cap
    hready.conductor_cap hready.puncture_cap
  change Scols=finiteColumns (Fintype.piFinset input.pools) at hScols
  change β=coefficient input (R0*C) seed at hβ
  dsimp only at hsource
  subst Scols β
  obtain ⟨family,hfamily,hbound⟩:=hsource
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm0 hml hm2 hwidth r hr1 hr2 hr3 hr4
  let Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
  have hEc:0≤Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient_nonneg
    Cc C₀ C₁ p T height (dc+degree+4*n) Z _ hCc.le hC₀ hC₁ hheight (zero_le_one.trans hz.le)
  have hpzero (j:Fin 2):p.profile j 0=0:=by
    by_contra hn
    exact (not_le_of_gt haPlain) ((p.support j hn).1)
  have hz1:input.W₁ 0=0:=by change src.W₁ 0=0;rw [←hp₁];exact hpzero 0
  have hz2:input.W₂ 0=0:=by change src.W₂ 0=0;rw [←hp₂];exact hpzero 1
  apply hbound χ₀ m hm0 hml hm2 Km (nominal input Km) hready.scale_pos hready.volume_cap
    hready.nominal_cap (le_refl _) hready.frequency_pos hready.frequency_cap
    (cost*(τ.modulus.absNorm:ℝ))
    (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
    Ec Ec hEc hEc ?_ ?_ r hr1 hr2 hr3 hr4
  all_goals
    intro q hq U dyad hphysical D0 hD0 hD0cap hD0sq χ v B₂ hB₂ alloc halloc
    have hg:=actual_common_gates input (R0*C) seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource _ _) _ _ q.property
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.1 (R0*C) (Or.inl rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.1.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.2 (R0*C) (Or.inr rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.2.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip

end SevenEighths.CenteredMomentEnergyCanonicalMainGaussian

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyCanonicalMainGaussian.actual_main_gaussian_from_bands_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyCanonicalMainGaussian.actual_main_gaussian_from_bands_oai.{u_1}
