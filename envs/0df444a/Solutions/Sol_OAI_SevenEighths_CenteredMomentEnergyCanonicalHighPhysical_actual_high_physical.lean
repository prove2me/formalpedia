-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:26:30.207626+00:00
-- url     : https://prove2.me/submissions/268a4387-dd69-449c-b140-5d4d9f80aa38

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalHighColumn_actual_admitted_subsets_high_column
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCanonicalHighSource_actual_original_left_high_column
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyFirstLiveAdmission_eventually_main_packet
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyFirstPhysicalNormalization_actual_physical_mass_of_columnBounds
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyFirstRightAdmission_eventually_right_error_packet
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstAmplificationChoice_eventually_dyadic_amplification

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
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

namespace ActualEisensteinCubic

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

open ConcreteTraceCRT

open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

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

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

end SevenEighths.CenteredMomentCanonicalFirst

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstScale
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem active_norm_pos (I J : Ideal O) :
    0<(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ) := by
  apply norm_pos
  exact Ideal.span_singleton_eq_bot.not.mpr (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)

theorem firstNominalScale_pos (I J E : Ideal O) (hE : E≠0) (K X : ℝ)
    (hK : 0<K) (hX : 0<X) : 0<firstNominalScale I J E K X := by
  unfold firstNominalScale
  exact div_pos (mul_pos (mul_pos (norm_pos E hE) (active_norm_pos I J)) (sq_pos_of_pos hX))
    (mul_pos (mul_pos hK (norm_pos _ (commonPart_ne_zero I J))) (norm_pos _ (commonPart_ne_zero J I)))

end SevenEighths.CenteredMomentFirstScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationMask
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem prime_coprime_iff (P : SmoothMobiusCorrection.PrimeIdeal) (J : Ideal O) :
    IsCoprime J P.val ↔ ¬P.val∣J := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

end SevenEighths.HeckeInverseAmplification

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeElements
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentPrimeElements
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentPrimePool CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O

theorem primaryPrime_data (P : Ideal O) (hp : Prime P) (hbad : P ∉ fixedBadPrimes) :
    Prime (primaryPrime P) ∧ Ideal.span {primaryPrime P} = P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ primaryPrime P - 1 ∧
    Supported (Ideal.span {primaryPrime P}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {primaryPrime P} ∧
    ringChar (O ⧸ Ideal.span {primaryPrime P}) ≠ 2 := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := (prime_good_iff_not_bad P).mpr hbad
  have hn := primaryPrime_ne_zero P hg.1
  have hs := (primaryPrime_spec P hn).2.2
  have hsupport : Supported P := by
    refine ⟨hp.ne_zero,?_⟩
    intro Q hQ
    have he : Q = P := by
      simpa only [UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
        normalize_eq,Multiset.mem_singleton] using hQ
    subst Q
    exact hg
  refine ⟨?_,hs.1,hs.2,?_,?_,?_⟩
  · apply (Ideal.span_singleton_prime hn).mp
    rw [hs.1]
    infer_instance
  · rwa [hs.1]
  · rw [hs.1]
    exact hg.1
  · rw [hs.1]
    exact hg.2

theorem elementPool_data (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (p : O) (hpm : p ∈ elementPool P) :
    Prime p ∧ Ideal.span {p} ∈ P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ p-1 ∧
    Supported (Ideal.span {p}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p} ∧
    ringChar (O ⧸ Ideal.span {p}) ≠ 2 := by
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hpm
  obtain ⟨hpr,hspan,hprim,hs,hg,hc⟩ := primaryPrime_data Q (hp Q hQ) (hbad Q hQ)
  exact ⟨hpr,hspan.symm ▸ hQ,hprim,hs,hg,hc⟩

end SevenEighths.CenteredMomentPrimeElements

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationSlotGap
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

theorem amplifier_not_dvd_slot (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell)
    (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ)) (hQN : (Ideal.absNorm Q:ℝ) ≤ b*Z^η) :
    ¬P∣Q := by
  intro hd
  have he := (prime_dvd_prime_iff_eq hP hQ).mp hd
  subst Q
  linarith

theorem live_profile_norm_bound (W : ℝ → ℂ) (b Z z η : ℝ) (I : Ideal O)
    (hb : 0 ≤ b) (hZ : 1 ≤ Z) (hz : z ≤ η)
    (hs : Function.support W ⊆ Set.Iic b)
    (hW : W ((Ideal.absNorm I:ℝ)/Z^z) ≠ 0) :
    (Ideal.absNorm I:ℝ) ≤ b*Z^η := by
  have hpow : 0 < Z^z := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  have h := (div_le_iff₀ hpow).mp (hs hW)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hz) hb)

end SevenEighths.CenteredMomentAmplificationSlotGap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentFirstCanonicalAllowance
open ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentActive CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonAllowance
local notation "O" => ActualEisensteinCubic.O

theorem activeConductor_span_product (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [activeConductor, span_finitePrimeModulus]
  exact Finset.prod_coe_sort (s := ActiveIndex I J)
    (f := fun P : CommonIndex I J => P.val)

theorem activeConductor_span_filter (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ (commonSupport I J).filter (fun P =>
        netExponent (CenteredExceptionalCount.valuation I P)
          (CenteredExceptionalCount.valuation J P) ≠ 0), P := by
  rw [activeConductor_span_product]
  simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
  exact Finset.prod_coe_sort (s := commonSupport I J)
    (f := fun P : Ideal O => if netExponent (CenteredExceptionalCount.valuation I P)
      (CenteredExceptionalCount.valuation J P) ≠ 0 then P else 1)

end SevenEighths.CenteredMomentFirstCanonicalAllowance

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open ConcretePrimeRowBridge CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFactor

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstAmplificationChoice.instDecidableEqSumFinOfNatNat_solutions
theorem errorIndex_cases (i : Fin 3) : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
  fin_cases i <;> simp [errorIndex]

theorem original_slot_coprime {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (Z sigma b eta : ℝ) (hZ : 1≤Z) (hb : 0≤b)
    (hgap : b*Z^eta<Z^(sigma/6))
    (z : ι → ℝ) (hz : ∀i,z i≤eta) (hlen : ∀i,D.lengths i=Z^(z i))
    (hsupp : ∀i,Function.support (D.slot i)⊆Set.Iic b)
    (hslot : ∀i,∀I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0)
    (hprime : ∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q : Ideal O) (hQ : Prime Q) (hQN : Z^(sigma/6)≤(Ideal.absNorm Q:ℝ)) :
    ∀i,∀I∈D.S (Sum.inl i),IsCoprime Q I := by
  intro i I hI
  have hW := hslot i I hI
  rw [hlen] at hW
  have hN := live_profile_norm_bound (D.slot i) b Z (z i) eta I hb hZ (hz i) (hsupp i) hW
  exact ((HeckeInverseAmplification.prime_coprime_iff ⟨Q,hQ⟩ I).mpr
    (amplifier_not_dvd_slot Q I hQ (hprime i I hI) Z (sigma/6) eta b hgap hQN hN)).symm

namespace OriginalData
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstAmplificationChoice.instDecidableEqSumFinOfNatNat_solutions
theorem active_subset (D : OriginalData ι) (i : ι ⊕ Fin 2) : D.active.S i⊆D.S i := by
  cases i <;> simp only [active]
  · exact Finset.filter_subset _ _
  · exact fun _ h => h

theorem active_slot (D : OriginalData ι) (i : ι) (I : Ideal O) (hI : I∈D.active.S (Sum.inl i)) :
    D.active.slot i ((Ideal.absNorm I:ℝ)/D.active.lengths i)≠0 :=
  (Finset.mem_filter.mp hI).2

end OriginalData

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic

end SevenEighths.CenteredMomentFirstAmplificationChoice

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

local instance instDecidableEq_solutions_r40e641_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
lemma live_card_le (B : Tuple ι) : Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa only [Fintype.card_coe] using (Finset.card_le_univ (liveIndices B))

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O"=>ActualEisensteinCubic.O

lemma mem_retainedIndices (R:ℝ)(n:ℤ):
    n∈retainedIndices R↔Retained R n ∧ ∃q:ℝ,1≤q ∧ dyadicWeight n q≠0 :=
  (finite_retained_integral_dyads R).mem_toFinset

end SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=>P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)

theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0<K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyInputParentCapacity
open CenteredMomentEnergyBands CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
variable {ι:Type*} [Fintype ι]

lemma raw_log_le_length (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    Real.logb Z X≤length Z X :=
  Real.logb_le_logb_of_le hZ hX (le_max_right _ _)

theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

theorem input_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [input_volume_log]
  have h1:=raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h2:=raw_log_le_length Z s.X₂ hZ s.X₂_pos
  nlinarith

theorem original_volume_cap (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(hk:1/6≤κ)
    (hP:∀i,1≤ s.P i)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    volume s≤Z^M := by
  have hh:=input_affine_capacity s Z κ M hZ hcap
  have hn:0≤∑i,Real.logb Z (s.P i):=
    Finset.sum_nonneg (fun i _=>Real.logb_nonneg hZ (hP i))
  have hp:0≤(6*κ-1)*(∑i,Real.logb Z (s.P i)):=mul_nonneg (by linarith) hn
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (by linarith)

end SevenEighths.CenteredMomentEnergyInputParentCapacity

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedRoot
open CanonicalQuadraticSieve CenteredMomentFirstMixedAllowance
open CenteredMomentFirstCanonicalAllowance
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily
open CenteredMomentFirstScale CenteredMomentSupportedCorrelation
local notation "O"=>HeckeFamily.O

lemma active_span_swap (C D:Ideal O):
    Ideal.span {activeConductor D C}=Ideal.span {activeConductor C D}:=by
  rw [activeConductor_span_filter,activeConductor_span_filter,
    CenteredMomentCompleteCommon.commonSupport_comm D C]
  congr 1
  apply Finset.filter_congr
  intro P hP
  simp only [CenteredMomentActive.netExponent]
  omega

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentFirstMixedRoot

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_frequency_radius_cap (I J:Ideal O)(E:Finset (CommonIndex I J))
    (K V Z B ξ:ℝ)(hK:0<K)(hV:0≤V)(hZ:1≤Z)
    (hVcap:V≤Z^B)(hKcap:K⁻¹≤Z^B):
    frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K V) Z ξ≤Z^(3*B+ξ/2) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hT:V^2/K≤Z^(3*B):=by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV hVcap 2) hKcap
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  unfold frequencyRadius
  calc
    _≤Z^(3*B)*Z^(ξ/2):=mul_le_mul_of_nonneg_right
      ((first_nominal_scale_le I J E K V hK).trans hT) (Real.rpow_nonneg hz.le _)
    _=_:=by rw [←Real.rpow_add hz]

open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair

lemma input_radius_cap {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B Z:ℝ)(s:Input ι)
    (hhi:∀i,|s.hi i|≤hi i)(hb₁:|s.b₁|≤b₁)(hb₂:|s.b₂|≤b₂)
    (hZ:1≤Z)(hfixed:(∏i,hi i)*b₁*b₂≤Z)
    (hV:volume s.toData≤Z^B):sourceRadius s≤Z^(B+1) := by
  have hVol:0<volume s.toData:=volume_pos s.toData
  have he:sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*volume s.toData:=by
    unfold sourceRadius volume;ring
  rw [he]
  have hprod:|∏i,s.hi i|≤∏i,hi i:=by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>hhi i)
  have hb₁0:0≤b₁:=(abs_nonneg _).trans hb₁
  have hp0:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>(abs_nonneg _).trans (hhi i))
  have hbound:|(∏i,s.hi i)*s.b₁*s.b₂|≤(∏i,hi i)*b₁*b₂:=by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hprod hb₁ (abs_nonneg _) hp0) hb₂
      (abs_nonneg _) (mul_nonneg hp0 hb₁0)
  have hcoeff:(∏i,s.hi i)*s.b₁*s.b₂≤Z:=
    (le_abs_self _).trans (hbound.trans hfixed)
  calc
    _≤Z*Z^B:=mul_le_mul hcoeff hV hVol.le (zero_le_one.trans hZ)
    _=Z^(B+1):=by rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hZ))];ring

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

universe u
namespace SevenEighths.CenteredMomentEnergyFirstAnnularAdmission
open HeckeFamily ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_r40e641_1 : DecidableEq (ι⊕Fin 2):=Classical.decEq _
omit [DecidableEq ι] in
lemma source_dyad_retained (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Retained (localRadius s R seed K Z ξ p E) (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  exact ((mem_retainedIndices _ _).mp hn).1

omit [DecidableEq ι] in
lemma source_dyad_gt_one (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):1<dyadicScale (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  obtain ⟨q,hq,hweight⟩:=((mem_retainedIndices _ _).mp hn).2
  exact hq.trans_lt ((dyadicWeight_support (n 1)) hweight).2

omit [DecidableEq ι] in
lemma source_nominal_positive (s:Input ι)(R seed:Ideal O)(K:ℝ)(hK:0<K)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    0<firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData):=by
  have he:=Ideal.span_singleton_eq_bot.not.mpr
    (primeSubsetGenerator_ne_zero (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using he
  exact firstNominalScale_pos _ _ _ hE K _ hK (volume_pos s.toData)

omit [DecidableEq ι] in
lemma source_nominal_span (s:Input ι)(R seed:Ideal O)(K:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)=
      firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (volume s.toData):=by rw [primeSubsetGenerator,span_idealGenerator]

omit [DecidableEq ι] in
theorem source_amplifier_packet (A D ξcap Z:ℝ)(hZ:32≤Z)
    (s:Input ι)(R seed:Ideal O)(K ξ:ℝ)(hK:0<K)(hξ:ξ≤ξcap)
    (hV:volume s.toData≤Z^A)(hKi:K⁻¹≤Z^D)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
    0<Tsec ∧ 0<dyadicScale (n 1) ∧
      dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
      8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
      Tsec≤1*firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (volume s.toData):=by
  have hz:1≤Z:=by linarith
  have hzpos:0<Z:=by linarith
  have hfreq:=retained_scale_le _ (n 1) (source_dyad_retained s R seed K Z ξ p E n)
  have hV':volume s.toData≤Z^(max A D):=hV.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _))
  have hKi':K⁻¹≤Z^(max A D):=hKi.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _))
  have hrad:=local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z
    (max A D) ξ hK (volume_pos s.toData).le hz hV' hKi'
  have hrad':localRadius s R seed K Z ξ p E≤Z^(3*max A D+ξcap/2):=by
    apply hrad.trans
    exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  refine ⟨source_nominal_positive s R seed K hK p E,dyadicScale_pos _,hfreq,?_,?_⟩
  · calc
      _≤32*Z^(3*max A D+ξcap/2):=by linarith
      _≤Z*Z^(3*max A D+ξcap/2):=
        mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hzpos.le _)
      _=Z^(amplifierCap A D ξcap):=by
        unfold amplifierCap
        rw [Real.rpow_add_one hzpos.ne']
        ring
  · rw [one_mul]
    exact (source_nominal_span s R seed K p E).le

theorem fixed_endpoint_radius (N:ℕ)(upper b₁ b₂ A Z:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂)(hZ:32≤Z)
    (hfixed:upper^N*b₁*b₂≤Z)
    (s:Input ι)(hN:Fintype.card ι≤N)
    (hhi:∀i,|s.hi i|≤upper)(hs₁:|s.b₁|≤b₁)(hs₂:|s.b₂|≤b₂)
    (hV:volume s.toData≤Z^A):sourceRadius s≤Z^(A+1):=by
  apply input_radius_cap (fun _:ι=>upper) b₁ b₂ A Z s hhi hs₁ hs₂ (by linarith) _ hV
  have hpow:upper^(Fintype.card ι)≤upper^N:=pow_le_pow_right₀ hu hN
  simpa only [Finset.prod_const,Finset.card_univ] using
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hb₁) hb₂).trans hfixed

theorem eventually_source_admission (N:ℕ)(upper b₁ b₂ A D ξcap:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(α:Type u)[Fintype α][DecidableEq α],∀s:Input α,Fintype.card α≤N →
      (∀i,|s.hi i|≤upper) → |s.b₁|≤b₁ → |s.b₂|≤b₂ →
      ∀(R seed:Ideal O)(K ξ:ℝ),0<K → ξ≤ξcap →
      volume s.toData≤Z^A → K⁻¹≤Z^D →
      sourceRadius s≤Z^(A+1) ∧
      ∀(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
        (n:SourceBlocks s R seed K Z ξ p E),
      let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
      0<Tsec ∧ 1<dyadicScale (n 1) ∧
        dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
        8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
        Tsec≤1*firstNominalScale p.val.1 p.val.2
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
          K (volume s.toData):=by
  filter_upwards [eventually_ge_atTop (32:ℝ),eventually_ge_atTop (upper^N*b₁*b₂)] with Z hZ hf
  refine ⟨by linarith,?_⟩
  intro α _ _ s hN hhi hs₁ hs₂ R seed K ξ hK hξ hV hKi
  refine ⟨fixed_endpoint_radius N upper b₁ b₂ A Z hu hb₁ hb₂ hZ hf s hN hhi hs₁ hs₂ hV,?_⟩
  intro p E n
  have hh:=source_amplifier_packet A D ξcap Z hZ s R seed K ξ hK hξ hV hKi p E n
  exact ⟨hh.1,source_dyad_gt_one s R seed K Z ξ p E n,hh.2.2⟩

end SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstLiveAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm
local notation "O" => HeckeFamily.O

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission.instDecidableEqSumFinOfNatNat_solutions
lemma lower_profile_zero (W : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (h : ∀ x, W x ≠ 0 → a ≤ x) : W 0 = 0 := by
  by_contra hn
  exact (not_le_of_gt ha) (h 0 hn)

theorem main_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    ∀ I : Ideal O, coefficient (child s C R B τ t) (R*C) seed I ≠ 0 →
      lowerFactor N l a * volume (child s C R B τ t) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (child s C R B τ t)
    ((live_card_le B.val).trans hc) hs hW₁ hW₂ (R*C) seed I hI

end SevenEighths.CenteredMomentEnergyFirstLiveAdmission

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedRightTransport
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstPhysicalSource CenteredMomentFirstMixedRoot
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstMixedAllowance
open CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

lemma swapSubset_product (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    (∏P∈swapSubset C D E,P.val)=∏P∈E,P.val := by
  simp only [swapSubset,Finset.prod_map,Equiv.toEmbedding_apply,swapIndex_val]

lemma swapSubset_generator (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    primeSubsetGenerator (fun P : CommonIndex D C=>P.val) (swapSubset C D E)=
      primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E := by
  unfold primeSubsetGenerator
  rw [swapSubset_product]

lemma swapped_modulus_factor (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
      (swapSubset C D E)*activeConductor D C}=
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} := by
  rw [swapSubset_generator,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_mul_span_singleton,active_span_swap]

theorem right_modulus (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayFourExpansion.RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    F.right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
        (swapSubset C D E)*activeConductor D C} := by
  rw [swapped_modulus_factor]
  exact F.right_modulus

lemma nominal_swap (C D E : Ideal O) (K X : ℝ) :
    firstNominalScale D C E K X=firstNominalScale C D E K X := by
  unfold firstNominalScale
  rw [active_span_swap]
  congr 1
  ring

end SevenEighths.CenteredMomentFirstMixedRightTransport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstRightAdmission
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstRightAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentFirstMixedRightTransport
local notation "O" => HeckeFamily.O

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyFirstRightAdmission.instDecidableEqSumFinOfNatNat_definitions
lemma main_radius_right (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) :
    columnMainRadius C D E K V Z σ δ reserve true =
      mainRadius D C (swapSubset C D E) K V Z σ δ reserve := by
  simp only [columnMainRadius, columnIdeal, oppositeIdeal, ite_true,
    mainRadius, swapSubset_generator, nominal_swap]

theorem eventually_right_main_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed0 : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed0 →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂,
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → 0 ≤ ξ → ξ ≤ 1 →
      0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ B : actualAllocations s.pools D, ∀ t : ℝ, ∀ innerL : Ideal O,
      frozenCoefficient B.val D R s.ν s.W s.P ≠ 0 →
      let Km := mainRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve
      F.right.modulus = s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C => P.val)
          (swapSubset C D E)*activeConductor D C} ∧
      Ready (child s D R B F.right t) (R*D) Km Z ξ (readyBudget A P) ∧
      (∀ I : Ideal O, coefficient (child s D R B F.right t) (R*D) innerL I ≠ 0 →
        lowerFactor N l a * volume (child s D R B F.right t) ≤ (I.absNorm : ℝ)) := by
  filter_upwards [eventually_main_packet N b b₁ b₂ l a A P hb hb₁ hb₂ hl ha hA hP] with Z hz
  refine ⟨hz.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock B t innerL hB
  dsimp only
  have hh := hz.2 s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F F.right (Or.inr rfl)
    K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1 hreserve hsec rows W n hn hblock
    true B t hB
  refine ⟨right_modulus s.η C D hC E ξ₁ ξ₂ F, ?_,
    main_lower_support N l a hl ha s hc hs hW₁ hW₂ D R innerL B F.right t⟩
  have hr : Ready (child s D R B F.right t) (R*D)
      (columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve true)
      Z ξ (readyBudget A P) := hh.1
  rw [main_radius_right] at hr
  exact hr

end SevenEighths.CenteredMomentEnergyFirstRightAdmission

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalRightSourceColumn
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
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
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
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

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentEnergyFirstRightAdmission

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn.instDecidableEqSumFinOfNatNat_definitions
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn.instFiniteQuotientOIdeal
theorem actual_original_right_high_column
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
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤ sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤ src.X₁ → Z^(Mwidth/4)≤ src.X₂ →
    Z^(Mwidth/4)≤ src.Y₁ → Z^(Mwidth/4)≤ src.Y₂ →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(D.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance D C Z);
    (commonEnergy (original src R0 seed0) D hD τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=CenteredMomentEnergyCanonicalHighColumn.actual_admitted_subsets_high_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_right_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=eventually_right_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ t
  subst τ
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedD:seed0∣D:=hcols.2.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hND:(D.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.2.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤ sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤ sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  let Es:=swapSubset C D E
  have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
    exact right_modulus src.η C D hC E χ₁ χ₂ F
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
  have hnom:firstNominalScale D C
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
      firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
    dsimp only [Es]
    rw [swapSubset_generator,nominal_swap]
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
        K (volume src)) Z ξ:=by
    rw [hnom]
    simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap hND Es hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedD
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock B t seed hB
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hm.2.1
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    let input:=child src D R0 B F.right t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hz:∀j,z j≤eta:=fun j=>hweta j.val
    have hlen:∀j,input.P j=Z^(z j):=fun j=>hmatch.scale j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hslot:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact original_slot_coprime (original input (R0*D) seed).active Z sigma (max 1 bslot) eta
        hZ.le (by positivity) hseparate z hz hlen hsupp
        (original input (R0*D) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*D) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun j=>n j) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
      (errorIndex i+1) hk' hslot Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hN)
    rcases he.2 with hdead|hlive
    · exact Or.inl hdead.1
    · exact Or.inr (by simpa only [mul_one] using hlive.1)

end SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstColumnPairing
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstColumnPairing
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy
open CenteredMomentFirstMixedAllowance CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondRetainedAggregate CenteredMomentChildAssembly
open CenteredMomentFirstNonexceptionalWeightSum
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_r40e641_2 : DecidableEq (ι⊕Fin 2):=Classical.decEq _
lemma fixed_pair_moduli (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(χ:RayCharacter):
    (fixedPair η C D hC E χ χ).left.modulus=(fixedPair η C D hC E 1 1).left.modulus ∧
    (fixedPair η C D hC E χ χ).right.modulus=(fixedPair η C D hC E 1 1).right.modulus:=by
  constructor
  · rw [(fixedPair η C D hC E χ χ).left_modulus,
      (fixedPair η C D hC E 1 1).left_modulus]
  · rw [(fixedPair η C D hC E χ χ).right_modulus,
      (fixedPair η C D hC E 1 1).right_modulus]

lemma reference_sum (ref seed front Z:ℝ)(loss:Fin 4→ℝ)(v:ℝ)(J:ℕ):
    (ref/seed)*(front*∑j:Fin 4,Z^(loss j))*(1+|v|)^(2*J)=
      ((∑j:Fin 4,ref*(front*Z^(loss j)))/seed)*(1+‖v‖)^(2*J):=by
  rw [Real.norm_eq_abs]
  simp only [←Finset.mul_sum]
  ring

omit [DecidableEq ι] in
theorem column_bounds_of_reference_sums
    (s:Input ι)(R seed:Ideal O)(Z:ℝ)(Jleft Jright:ℕ)
    (frontLeft frontRight:ℝ)(lossLeft lossRight:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ)
    (hleft:∀L:Ideal O,(L.absNorm:ℝ)≤ sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.1 (supported s R seed p).1
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.1.absNorm:ℝ))^2*Z^(allowance p.val.1 p.val.2 Z)/(L.absNorm:ℝ))*
          (frontLeft*∑j:Fin 4,Z^(lossLeft j))*(1+|v|)^(2*Jleft))
    (hright:∀L:Ideal O,(L.absNorm:ℝ)≤ sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.2 (supported s R seed p).2
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.2.absNorm:ℝ))^2*Z^(allowance p.val.2 p.val.1 Z)/(L.absNorm:ℝ))*
          (frontRight*∑j:Fin 4,Z^(lossRight j))*(1+|v|)^(2*Jright)):
    ColumnBounds s R seed Z Jleft Jright
      (fun j=>frontLeft*Z^(lossLeft j)) (fun j=>frontRight*Z^(lossRight j)) p E n:=by
  constructor
  · intro L _ hcap hL χ v
    have hh:=hleft L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).1] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)
  · intro L _ hcap hL χ v
    have hh:=hright L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).2] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)

end SevenEighths.CenteredMomentEnergyFirstColumnPairing

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalHighPhysical
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighPhysical
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
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
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
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

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPower
open CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstNonexceptionalLocalWeightSum

local instance instDecidableEqSumFinOfNatNat_solutions_r40e641_3 {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical.instFiniteQuotientOIdeal
theorem actual_high_physical_oai
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
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(εphysical lowerProduct:ℝ)
    (hεphysical:0<εphysical)(hlowerProduct:0<lowerProduct):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cphysical:ℝ,0<Cphysical ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    lowerProduct≤(∏i,src.lo i)*a*a →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 → seed0≠0 →
    ∀K:ℝ,1≤K →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip ell:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤ src.X₁ → Z^(Mwidth/4)≤ src.X₂ →
    Z^(Mwidth/4)≤ src.Y₁ → Z^(Mwidth/4)≤ src.Y₂ →
    (∀j:Fin 4,
      CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma (frequencyLoss Z 32 ξ) reserve
        ((readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
          (frequencyLoss Z 32 ξ+reserve+θsource)/6+θclip/3+κ*mesh)
        εsrc A saving j + εsrc*(A+1)+primeLoss ≤ ell) →
    CenteredMomentFirstSourceReduction.physicalMass src R0 seed0 fixedBadMask 1 (Ψ Aorig) K Z ξ /
      volume src ≤ Cphysical*(C₀+C₁+1)*(p.control Uprofile)^2*
        (1+|src.t|+height)^Jheight*Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
  obtain ⟨UL,JL,hleft⟩:=CenteredMomentEnergyCanonicalHighSource.actual_original_left_high_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  obtain ⟨UR,JR,hright⟩:=CenteredMomentEnergyCanonicalRightSourceColumn.actual_original_right_high_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  have hphysical (T:Finset α):=CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
    (ι:=T) (Ψ T) JL JR (fun i=>|highs i.val|) (max 1 b) (max 1 b) A ξ εphysical
    lowerProduct hA hξ.le hεphysical hlowerProduct
  choose Cp hCp hp using hphysical
  let Cmass:ℝ:=1+∑T:Finset α,Cp T
  have hCmass:0<Cmass:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
    dsimp [Cmass];linarith
  have hCpCap (T:Finset α):Cp T≤Cmass:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
      (Finset.mem_univ T)
    dsimp [Cmass];linarith
  refine ⟨UL∪UR,2*(JL+JR),?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CL,hCL,ZL,hZL,hleft⟩:=hleft η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CR,hCR,ZR,hZR,hright⟩:=hright η₀ Q hQM hQ0 hQt hQ72
  have hmL:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JL
  have hmR:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JR
  let Cm:ℝ:=Cmass*(CL+CR)*(1+CenteredMomentSecondWindowBudget.profileMoment JL)*
    (1+CenteredMomentSecondWindowBudget.profileMoment JR)
  have hCm:0<Cm:=by dsimp [Cm];positivity
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hp
  obtain ⟨Zp,hZp⟩:=Filter.eventually_atTop.mp hall
  refine ⟨Cm,hCm,max Zp (max ZL ZR),lt_of_lt_of_le hZL
    ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max hprod R0 seed0 hR0 hRcap hseed0 hseed00 K hK1 p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip ell hθclip hMA hcap hMdecl hMwidth hdrop
    hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ hfit
  have hZL':ZL≤Z:=(le_max_left _ _).trans ((le_max_right _ _).trans hZZ)
  have hZR':ZR≤Z:=(le_max_right _ _).trans ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hZL.trans_le hZL'
  have hz:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs (by
    have hh:=hcap.trans hMA
    simpa only [hmatch.scale,Real.logb_rpow hz hZ.ne'] using hh)
  have hKi:K⁻¹≤Z^A:=(inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le hA)
  have hs₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx;rw [←hp₁] at hx;exact (p.support 0 hx).1
  have hs₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx;rw [←hp₂] at hx;exact (p.support 1 hx).1
  let delta:=frequencyLoss Z 32 ξ
  let paid:=(readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
    (delta+reserve+θsource)/6+θclip/3+κ*mesh
  let powers:Fin 4→ℝ:=fun j=>
    CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma delta reserve paid εsrc A saving j
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let base:=εsrc*(A+1)+primeLoss
  let FL:=CL*(C₀+C₁+1)*(p.control UL)^2*(1+height)^JL
  let FR:=CR*(C₀+C₁+1)*(p.control UR)^2*(1+height)^JR
  let Fcap:ℝ:=(CL+CR)*(C₀+C₁+1)*(p.control (UL∪UR))^2*(1+height)^(JL+JR)
  let frontL:=FL*Z^(deficit+base)
  let frontR:=FR*Z^(deficit+base)
  have hfrontL:0≤frontL:=by dsimp [frontL,FL];positivity
  have hfrontR:0≤frontR:=by dsimp [frontR,FR];positivity
  have hFcap:0≤Fcap:=by dsimp [Fcap];positivity
  have hcontrol (S₁:Finset (ℕ×ℕ))(hs:S₁⊆UL∪UR):p.control S₁≤p.control (UL∪UR):=by
    unfold Profiles.control
    exact mul_le_mul
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hFL:FL≤Fcap:=by
    dsimp [FL,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UL
    · exact hcontrol UL Finset.subset_union_left
    · linarith
    · omega
  have hFR:FR≤Fcap:=by
    dsimp [FR,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UR
    · exact hcontrol UR Finset.subset_union_right
    · linarith
    · omega
  have hcoeff (F:ℝ)(hF:F≤Fcap)(j:Fin 4):
      (F*Z^(deficit+base))*Z^(powers j)≤Fcap*Z^(deficit+ell):=by
    rw [mul_assoc,←Real.rpow_add hz]
    apply mul_le_mul hF (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) (Real.rpow_nonneg hz.le _) hFcap
    have hh:powers j+base≤ell:=by
      dsimp [powers,base,paid,delta]
      linarith [hfit j]
    linarith
  have hcols (lab:CenteredMomentFirstNonexceptionalWeightSum.Labels src R0 seed0)
      (E:Finset (CommonIndex lab.val.1 lab.val.2))
      (n:CenteredMomentFirstReferenceSource.SourceBlocks src R0 seed0 K Z ξ lab E)
      (hne:originalBlock src R0 seed0 (Ψ T) K Z ξ lab E n≠0):
      CenteredMomentFirstReferenceEnergy.ColumnBounds src R0 seed0 Z JL JR
        (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) lab E (fun i=>(n i).val):=by
    apply CenteredMomentEnergyFirstColumnPairing.column_bounds_of_reference_sums
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hleft T θ Z hZL' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.left (Or.inl rfl)
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ v
      simpa only [frontL,FL,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hright T θ Z hZR' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.right rfl
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ v
      simpa only [frontR,FR,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hmass:=(hZp Z ((le_max_left _ _).trans hZZ) T) src R0 seed0 hseed0 hseed00
    (fun i=>by rw [hhiSrc]) (by rwa [abs_of_nonneg hb1]) (by rwa [abs_of_nonneg hb2])
    a a K haPlain haPlain hK hprod hs₁ hs₂ hV hKi Fcap Mdecl ell (fun _=>ell) (fun _=>ell)
    (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) hFcap
    (fun j=>mul_nonneg hfrontL (Real.rpow_nonneg hz.le _))
    (fun j=>mul_nonneg hfrontR (Real.rpow_nonneg hz.le _))
    (hcoeff FL hFL) (hcoeff FR hFR) (fun _=>le_rfl)
    (fun _=>le_rfl) (fun lab E _ n hne=>hcols lab E n hne)
  have hconst:Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
      CenteredMomentSecondWindowBudget.profileMoment JR≤Cm:=by
    dsimp [Cm]
    gcongr
    · exact hCpCap T
    · linarith
    · linarith
  have hheightProduct:(1+height)^(JL+JR)*(1+|src.t|)^(JL+JR)≤
      (1+|src.t|+height)^(2*(JL+JR)):=by
    have heq:(1+|src.t|+height)^(2*(JL+JR))=
        (1+|src.t|+height)^(JL+JR)*(1+|src.t|+height)^(JL+JR):=by
      rw [show 2*(JL+JR)=(JL+JR)+(JL+JR) by omega]
      exact pow_add _ _ _
    rw [heq]
    apply mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg src.t]) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  calc
    _ ≤ (Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
          CenteredMomentSecondWindowBudget.profileMoment JR)*(C₀+C₁+1)*
          (p.control (UL∪UR))^2*((1+height)^(JL+JR)*(1+|src.t|)^(JL+JR))*
          Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
      apply hmass.trans_eq
      dsimp [Fcap]
      ring
    _ ≤ _ := by gcongr

end SevenEighths.CenteredMomentEnergyCanonicalHighPhysical

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical_oai.{u_1}
