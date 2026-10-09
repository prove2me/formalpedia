-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyFirstRightAdmission.eventually_right_error_packet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:47:04.614525+00:00
-- url     : https://prove2.me/submissions/bf06eaeb-aac4-4666-bd39-4c4137c864a7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstSecondActiveErrorGates_eventually_active_error_ready

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem source_enclosure_power (Z Csec L ξ Nv : ℝ) (hZ : 1 < Z) (hC : 0 < Csec) (hNv : 0 < Nv) :
    4*(Csec*Z^L)*Z^(ξ/2)/Nv=Z^(L-Real.logb Z Nv+frequencyLoss Z Csec ξ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [frequencyLoss,show L-Real.logb Z Nv+(ξ/2+Real.logb Z (4*Csec))=
    (L+ξ/2)+Real.logb Z (4*Csec)-Real.logb Z Nv by ring,
    Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz (ne_of_gt hZ),Real.rpow_logb hz (ne_of_gt hZ)]
  · ring
  · exact hNv
  · positivity

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass
namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LogDyadic
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

end SevenEighths.CenteredMomentLogDyadic

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

theorem primePool_data (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : fixedBadPrimes ⊆ S) (a b x : ℝ)
    (Q : Ideal O) (hQ : Q ∈ primePool M H S a b x) :
    Prime Q ∧ Q ∉ fixedBadPrimes := by
  obtain ⟨hQ,hQS⟩ := Finset.mem_sdiff.mp hQ
  exact ⟨((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp hQ).2.1,
    fun hbad => hQS (hS hbad)⟩

end SevenEighths.CenteredMomentPrimeElements

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
open CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O

theorem dyadRows_ne_zero (n : ℤ) (h : O) (hh : h∈dyadRows n) : h≠0 := by
  intro he
  have hn := (mem_dyadRows n h).mp hh
  subst h
  exact hn (by simpa [normValue] using dyadicWeight_zero_nonpos n 0 le_rfl)

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open ConcretePrimeRowBridge CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFactor

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstAmplificationChoice.instDecidableEqSumFinOfNatNat_solutions
theorem pool_prime_log_range (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (Z sigma : ℝ) (hZ : 1<Z) (p : O)
    (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
    0≤Real.logb Z (normValue p) ∧ Real.logb Z (normValue p)≤ sigma/3 := by
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p hp
  have hb := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3)) (Finset.mem_sdiff.mp hd.2.1).1
  have hu : normValue p≤Z^(sigma/3) := by simpa only [normValue,mul_one] using hb.2
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one p hd.1.ne_zero),?_⟩
  have hh := Real.logb_le_logb_of_le hZ (normValue_pos p hd.1.ne_zero) hu
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hh

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

local instance instDecidableEq_solutions_r7d7c41_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
lemma live_card_le (B : Tuple ι) : Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa only [Fintype.card_coe] using (Finset.card_le_univ (liveIndices B))

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

theorem original_beta (s : Input ι) (R seed : Ideal O) :
    (original s R seed).beta=coefficient s R seed := rfl

lemma radius_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤
      (b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s :=
  radius_le N b b₁ b₂ hb (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc he.2.1
    (fun i=>(s.upper_ge i).trans he.1) he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 he.2.2.2.2.2

theorem eventual_geometry (G ε : ℝ) (hG : 1≤G) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ G≤Z^ε ∧ G^2≤Z^ε := by
  have hh:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (G^2)
  filter_upwards [eventually_gt_atTop (1:ℝ),hh] with Z hZ hpow
  exact ⟨hZ,(by nlinarith : G≤G^2).trans hpow,hpow⟩

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
namespace SevenEighths.CenteredMomentSecondRadicalBudget
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondMovingSupport
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows CenteredMomentPartitionNorm
open CenteredMomentHeckeColumnWindow RayFourExpansion CenteredMomentCommonSupport CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_modulus_bound (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm≤η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  have hn : η.modulus*Ideal.span {(12:O)}≠0 := mul_ne_zero η.modulus_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  have hd : (childCharacter η χ).modulus∣η.modulus*Ideal.span {(12:O)} := by
    apply Ideal.dvd_iff_le.mpr
    exact le_inf Ideal.mul_le_left Ideal.mul_le_right
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) (map_dvd Ideal.absNorm hd)

end SevenEighths.CenteredMomentSecondRadicalBudget

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePresentation
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily
local notation "O"=>ActualEisensteinCubic.O

theorem fixedPresentationCost_pos : 0<fixedPresentationCost:=by
  apply mul_pos
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using fixedBadMask_ne_zero))
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simp))

theorem fixed_presentation_norm (η τ:Character)(C D:Ideal O)(E:Finset (CommonIndex C D))
    (hM:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ.modulus.absNorm:ℝ)=fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=by
  rw [hM,←Ideal.span_singleton_mul_span_singleton]
  simp only [map_mul,Nat.cast_mul,eisEmbedding_norm_sq_eq_absNorm_span,fixedPresentationCost]
  ring

theorem fixed_pair_presentation_caps (η τ₁ τ₂:Character)(C D:Ideal O)
    (E:Finset (CommonIndex C D))
    (hM₁:τ₁.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hM₂:τ₂.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ₁.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (τ₂.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  ⟨(fixed_presentation_norm η τ₁ C D E hM₁).le,(fixed_presentation_norm η τ₂ C D E hM₂).le⟩

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem FixedPair.conductor_caps {η:Character}{C D:Ideal O}{hC:Supported C}
    {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}(F:FixedPair η C D hC E ξ₁ ξ₂):
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  fixed_pair_presentation_caps η F.left F.right C D E F.left_modulus F.right_modulus

variable {ι:Type*}[Fintype ι]

end SevenEighths.CenteredMomentFirstPhysicalSource

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstSourceConductorCaps
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily
local notation "O"=>ActualEisensteinCubic.O

lemma divisor_norm_le (I C : Ideal O) (hC : C≠0) (h : I∣C) :
    (I.absNorm:ℝ)≤C.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm h)

lemma original_factor_caps (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) :
    ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2≤C.absNorm ∧
    ‖eisEmbedding (activeConductor C D)‖^2≤C.absNorm := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span]
  exact ⟨divisor_norm_le _ C hC.1 ((subsetGenerator_span_dvd C D E).trans (commonPart_dvd C D hC.1)),
    divisor_norm_le _ C hC.1 ((activeConductor_span_dvd C D).trans (commonPart_dvd C D hC.1))⟩

theorem fixed_pair_caps (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
  have h:=original_factor_caps C D hC E
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2≤
      fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    have hf:=fixedPresentationCost_pos.le
    nlinarith [mul_le_mul h.1 h.2 (sq_nonneg _) (Nat.cast_nonneg C.absNorm),
      mul_nonneg hf (Nat.cast_nonneg η.modulus.absNorm)]
  exact ⟨F.conductor_caps.1.trans hb,F.conductor_caps.2.trans hb⟩

lemma rayCost_nonneg : 0≤ rayCost :=
  mul_nonneg (Nat.cast_nonneg _) fixedPresentationCost_pos.le

theorem radical_once_cap (ρ υ : Character) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤ rayCost*(ρ.modulus.absNorm:ℝ)*(Ideal.span {p}).absNorm := by
  have hP : (1:ℕ)≤(Ideal.span {p}).absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp))
  have ht : (if k=0 then 1 else (Ideal.span {p}).absNorm)≤(Ideal.span {p}).absNorm := by
    split_ifs <;> omega
  have hr:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hn : υ.modulus.absNorm≤
      (ρ.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    apply hυ.trans
    unfold radicalBound
    gcongr
  have hh : (υ.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    exact_mod_cast hn
  convert (preTransparency := .instances) hh using 1 ; unfold rayCost fixedPresentationCost ; ring

theorem fixed_error_cap (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) (ρ υ : Character)
    (hρ : ρ=F.left ∨ ρ=F.right) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤(rayCost*fixedPresentationCost)*
      (η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2*(Ideal.span {p}).absNorm := by
  have hf:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hr : (ρ.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    rcases hρ with rfl|rfl
    · exact hf.1
    · exact hf.2
  apply (radical_once_cap ρ υ χ p hp k hυ).trans
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr rayCost_nonneg)
    (Nat.cast_nonneg (Ideal.span {p}).absNorm)
  convert (preTransparency := .instances) hh using 1 ; ring

theorem eventually_caps (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀η:Character,∀(C D:Ideal O)(hC:Supported C),
    ∀(E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter)(F:FixedPair η C D hC E ξ₁ ξ₂),
    ∀q B:ℝ,(η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^B→
    (F.left.modulus.absNorm:ℝ)≤Z^(q+2*B+ε) ∧
    (F.right.modulus.absNorm:ℝ)≤Z^(q+2*B+ε) ∧
    ∀(ρ υ:Character), (ρ=F.left∨ρ=F.right)→∀(χ:RayCharacter)(p:O),p≠0→
    ∀(k:ℕ)(r:ℝ),υ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p k→
    ((Ideal.span {p}).absNorm:ℝ)≤Z^r→(υ.modulus.absNorm:ℝ)≤Z^(q+2*B+r+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε))
    (max fixedPresentationCost (rayCost*fixedPresentationCost))
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro η C D hC E ξ₁ ξ₂ F q B hη hCcap
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hm:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2≤Z^(q+2*B+ε) := by
    calc
      _≤Z^ε*Z^q*(Z^B)^2 := by
        gcongr
        exact (le_max_left _ _).trans hconst
      _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
  refine ⟨hm.1.trans hb,hm.2.trans hb,?_⟩
  intro ρ υ hρ χ p hp k r hυ hP
  apply (fixed_error_cap η C D hC E ξ₁ ξ₂ F ρ υ hρ χ p hp k hυ).trans
  calc
    _≤Z^ε*Z^q*(Z^B)^2*Z^r := by
      gcongr
      exact (le_max_right _ _).trans hconst
    _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentFirstSourceConductorCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

local instance instDecidableEq_solutions_r7d7c41_2 {α:Type*}:DecidableEq α:=Classical.decEq _
theorem normalized_zero {ι:Type*}[Fintype ι](s:Input ι)(R seed:Ideal O)
    (hz:∀I:Ideal O,(original s R seed).beta I=0)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource s R seed W K=0:=by
  simp [normalizedGaussSource,sourceGaussEnergy,gaussEnergy,gaussPolynomial,hz]

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicRows
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicRows
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm
local notation "O" => HeckeFamily.O

lemma mem_activeRows (rows : Finset O) (n : Fin 4→ℤ) (h : O) :
    h∈activeRows rows n ↔ h∈rows ∧ dyadicWeight (n 1) (normValue h)≠0 := by
  simp only [activeRows,Finset.mem_filter,mem_dyadRows]

lemma activeRows_nonzero (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) : h≠0 :=
  dyadRows_ne_zero (n 1) h (Finset.mem_filter.mp hh).2

lemma activeRows_norm (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤normValue h ∧ dyadicScale (n 1)/4<normValue h ∧ normValue h<dyadicScale (n 1) :=
  ⟨normValue_ge_one h (activeRows_nonzero rows n h hh),
    dyadicWeight_support (n 1) ((mem_activeRows rows n h).mp hh).2⟩

lemma activeRows_scale_gt_one (rows : Finset O) (n : Fin 4→ℤ)
    (hne : (activeRows rows n).Nonempty) : 1<dyadicScale (n 1) := by
  obtain ⟨h,hh⟩:=hne
  exact (activeRows_norm rows n h hh).1.trans_lt (activeRows_norm rows n h hh).2.2

lemma row_log_window (n : ℤ) (h : O) :
    logAnnulus (Real.log (‖eisEmbedding h‖^2/dyadicScale n)) =
      (dyadicWeight n (normValue h):ℂ) := by
  by_cases hh : h=0
  · subst h
    simp only [map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div,Real.log_zero,
      logAnnulus,Real.exp_zero]
    rw [annulus_zero_high 1 le_rfl]
    rw [show normValue (0:O)=0 by simp [normValue_eq_embedding],
      dyadicWeight_zero_nonpos n 0 le_rfl,Complex.ofReal_zero]
  · rw [←normValue_eq_embedding]
    exact (actual_dyadic_log_window n (normValue h)
      (zero_lt_one.trans_le (normValue_ge_one h hh))).symm

theorem block_activeRows (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) =
    block η m A t S c C D hC hD E (activeRows rows n) W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold block activeRows
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hd : h∈dyadRows (n 1)
  · simp only [hd,ite_true]
  · have hw : dyadicWeight (n 1) (normValue h)=0 := by
      simpa only [mem_dyadRows,not_not] using hd
    simp only [hd,windows,row_log_window,hw,Complex.ofReal_zero,
      mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

end SevenEighths.CenteredMomentFirstPhysicalDyadicRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedRadiusLower
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedRadiusLower
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicRows
local notation "O" => ActualEisensteinCubic.O

lemma base_radius_identity (Z K0 Csec xi : ℝ) (hZ : 1<Z) (hC : 0<Csec) :
    Z^(K0+frequencyLoss Z (32*Csec) xi)=128*Csec*Z^K0*Z^(xi/2) := by
  have h := source_enclosure_power Z (32*Csec) K0 xi 1 hZ (by positivity) zero_lt_one
  simpa only [Real.logb_one,sub_zero,div_one] using h.symm.trans (by ring)

lemma retained_base_le (Z K0 Csec Tsec xi H0 : ℝ) (hZ : 1<Z) (hC : 0<Csec)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi) :
    H0≤Z^(K0+frequencyLoss Z (32*Csec) xi) := by
  rw [base_radius_identity Z K0 Csec xi hZ hC]
  have hp : 0≤Z^(xi/2) := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hq : 0≤Z^K0 := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  calc
    H0≤4*(Tsec*Z^(xi/2)) := hrow
    _≤4*((Csec*Z^K0)*Z^(xi/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsec hp) (by norm_num)
    _≤128*Csec*Z^K0*Z^(xi/2) := by nlinarith [mul_nonneg (mul_nonneg hC.le hq) hp]

theorem common_radii_lower (Z d K0 c sigma reserve Csec Tsec xi H0 : ℝ)
    (hZ : 1<Z) (hC : 0<Csec) (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi)
    (p : O) (k : ℕ) :
    H0≤ mainCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve ∧
    H0≤errorCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve p k := by
  have hb := retained_base_le Z K0 Csec Tsec xi H0 hZ hC hsec hrow
  constructor
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c) (0:ℝ)]
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)]

theorem actual_retained_radii_lower (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (p : O) (k : ℕ) :
    dyadicScale n≤ mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve ∧
    dyadicScale n≤errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k := by
  apply common_radii_lower Z d _ c sigma reserve Csec Tsec xi _ hZ hC hsigma hreserve
  · simpa only [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)] using hsec
  · exact retained_scale_le _ n hn

theorem active_row_reciprocals (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (rows : Finset O) (n : Fin 4→ℤ)
    (hn : Retained (frequencyRadius Tsec Z xi) (n 1))
    (hne : (activeRows rows n).Nonempty) (p : O) (k : ℕ) :
    (mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve)⁻¹≤1 ∧
    (errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k)⁻¹≤1 := by
  have hb := actual_retained_radii_lower I J E hE K X Z Csec Tsec xi d c sigma reserve
    hK hX hZ hC hsigma hreserve hsec (n 1) hn p k
  have ho := (activeRows_scale_gt_one rows n hne).le
  exact ⟨inv_le_one_of_one_le₀ (ho.trans hb.1),inv_le_one_of_one_le₀ (ho.trans hb.2)⟩

end SevenEighths.CenteredMomentFirstAmplifiedRadiusLower

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
open CenteredMomentFirstAmplifiedRadiusLower CenteredMomentFirstScale
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
theorem first_block_active_rows_nonempty
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (n : Fin 4 → ℤ)
    (hne : block η m A t S c C D hC hD E rows W (fun _ => logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0) :
    (activeRows rows n).Nonempty := by
  by_contra h
  have he : activeRows rows n = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  apply hne
  rw [block_activeRows, he]
  simp only [block, Finset.sum_empty, mul_zero]

lemma error_exponent_le (A P σ ξ : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hσ : σ ≤ 1) (hξ : ξ ≤ 1) :
    exponent A 0 P (3*A+3+σ/3) 1 ξ ≤ readyBudget A P := by
  unfold exponent readyBudget
  exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

lemma ready_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (R : Ideal O)
    (K Z ξ B B' : ℝ) (hZ : 1 ≤ Z) (hB : B ≤ B')
    (h : Ready s R K Z ξ B) : Ready s R K Z ξ B' := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ hB
  exact ⟨h.puncture_ne,h.scale_pos,h.volume_cap.trans hp,h.source_nonneg,
    h.source_cap.trans hp,h.conductor_cap.trans hp,h.puncture_cap.trans hp,
    h.nominal_pos,h.nominal_cap.trans hp,h.frequency_pos,h.frequency_cap.trans hp⟩

lemma lower_profile_zero (W : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (h : ∀ x, W x ≠ 0 → a ≤ x) : W 0 = 0 := by
  by_contra hn
  exact (not_le_of_gt ha) (h 0 hn)

theorem error_lower_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a)
    (s : Input ι) (hc : Fintype.card ι ≤ N) (hs : l ≤ s.lower)
    (hW₁ : ∀ x, s.W₁ x ≠ 0 → a ≤ x) (hW₂ : ∀ x, s.W₂ x ≠ 0 → a ≤ x)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    ∀ I : Ideal O, coefficient (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed I ≠ 0 →
      lowerFactor N l a * volume (errorInput s C R B τ t Q k Bp υ v) ≤ (I.absNorm : ℝ) := by
  intro I hI
  exact actual_lower_support N l a hl ha (errorInput s C R B τ t Q k Bp υ v)
    ((live_card_le Bp.val).trans ((live_card_le B.val).trans hc))
    hs hW₁ hW₂ ((R*C)*(Q^k)) seed I hI

theorem eventual_parent_radius (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s →
      ∀ A : ℝ, volume s ≤ Z^A → sourceRadius s ≤ Z^(A+1) := by
  let G := b^N*b₁*b₂
  have hG : 1 ≤ G := by
    have hp : 1 ≤ b^N := one_le_pow₀ hb
    dsimp [G]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hb₁) hb₂
  filter_upwards [eventual_geometry G 1 hG (by norm_num)] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro ι _ _ s hc he A hV
  have hr := (radius_bound N b b₁ b₂ hb hb₁ hb₂ s hc he).2
  have hg : G ≤ Z := by simpa only [Real.rpow_one] using hZ.2.1
  apply hr.trans
  calc
    G * volume s ≤ Z * Z^A := mul_le_mul hg hV (volume_pos s).le (zero_lt_one.trans hZ.1).le
    _ = Z^(A+1) := by rw [Real.rpow_add_one (zero_lt_one.trans hZ.1).ne']; ring

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
open CenteredMomentFirstAmplifiedRadiusLower CenteredMomentFirstScale
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
theorem eventually_right_error_packet_oai (N : ℕ) (b b₁ b₂ l a A P : ℝ)
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
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → σ ≤ 1 →
      0 ≤ ξ → ξ ≤ 1 → 0 ≤ reserve →
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
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O)),
      fixedBadPrimes ⊆ Sbad →
      ∀ p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(σ/3))),
      ∀ k : ℕ, k = 1 ∨ k = 6 ∨ k = 7 →
      (∀ i, ∀ I ∈ (activeInput (child s D R B F.right t)).slots i, IsCoprime (Ideal.span {p}) I) →
      ∀ Bp : actualAllocations (activeInput (child s D R B F.right t)).pools ((Ideal.span {p})^k),
      ∀ (χ : RayCharacter) (υ : Character) (v : ℝ),
      υ.modulus.absNorm ≤ radicalBound (childCharacter F.right χ) fixedBadMask p (errorMovingExponent (k-1)) →
      let d := errorInput s D R B F.right t (Ideal.span {p}) k Bp υ v
      let Re := (R*D)*(Ideal.span {p})^k
      let Ke := errorRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve p k
      F.right.modulus = s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C => P.val)
          (swapSubset C D E)*activeConductor D C} ∧
      (((∀ I : Ideal O, coefficient d Re innerL I = 0) ∧ normalizedGaussSource d Re innerL ballProfile Ke = 0) ∨
      (Ready d Re Ke Z ξ (readyBudget A P) ∧
        (∀ I : Ideal O, coefficient d Re innerL I ≠ 0 →
          lowerFactor N l a * volume d ≤ (I.absNorm : ℝ)))) := by
  filter_upwards [eventually_active_error_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F K Csec Tsec σ ξ reserve hK hCsec hσ hσ1
    hξ hξ1 hreserve hsec rows W n hn hblock B t innerL hB M _ H Sbad hbad p hp k _hk
    hslot Bp χ υ v hυ
  dsimp only
  refine ⟨right_modulus s.η C D hC E ξ₁ ξ₂ F, ?_⟩
  let d := errorInput s D R B F.right t (Ideal.span {p}) k Bp υ v
  let Re := (R*D)*(Ideal.span {p})^k
  let Ke := errorRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve p k
  by_cases hdead : ∀ I : Ideal O, coefficient d Re innerL I = 0
  · exact Or.inl ⟨hdead, normalized_zero d Re innerL hdead ballProfile Ke⟩
  right
  have hlive : ∃ I : Ideal O, (original d Re innerL).beta I ≠ 0 := by
    simpa only [original_beta,not_forall] using hdead
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed0 hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : (D.absNorm : ℝ) ≤ Z^(A+1) := by
    exact hcdata.2.2.2.2.2.2.trans hH
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).2) p hp
  have hp0 : p ≠ 0 := hd.1.ne_zero
  have hQ : Ideal.span {p} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hpupper := (pool_prime_log_range M H Sbad hbad Z σ hz p hp).2
  have hPN : ((Ideal.span {p}).absNorm : ℝ) ≤ Z^(σ/3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le hpupper
    rwa [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz) (normValue_pos p hp0)] at hh
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have hv : (υ.modulus.absNorm : ℝ) ≤ Z^(3*A+3+σ/3) := by
    have hh := ht.2.2 F.right υ (Or.inr rfl) χ p hp0 (errorMovingExponent (k-1)) (σ/3) hυ hPN
    simpa only [show A+2*(A+1)+σ/3+1 = 3*A+3+σ/3 by ring] using hh
  have hE : Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*idealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z (C.absNorm : ℝ))
    (Real.logb Z (D.absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne p k).2
  have hKe : 0 < Ke := by
    dsimp [Ke,errorRadius,errorCommonRadius]
    positivity
  have hKeInv : Ke⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [Ke,errorRadius,swapSubset_generator,nominal_swap,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he D R innerL B F.right t hR hB _ hQ k hslot Bp υ v Ke
    A 0 P (3*A+3+σ/3) ξ hKe hξ hz₁ hz₂ hV hKeInv hRN hv hlive
  exact ⟨ready_mono _ _ Ke Z ξ _ _ hz.le (error_exponent_le A P σ ξ hA hP hσ1 hξ1) hr,
    error_lower_support N l a hl ha s hc hs hW₁ hW₂ D R innerL B F.right t _ k Bp υ v⟩

end SevenEighths.CenteredMomentEnergyFirstRightAdmission

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyFirstRightAdmission.eventually_right_error_packet_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyFirstRightAdmission.eventually_right_error_packet_oai.{u_1}
