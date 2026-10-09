-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCommonPairedSource.whole_paired_columns
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:25:41.909986+00:00
-- url     : https://prove2.me/submissions/2d651556-85a0-4e1b-8cbf-bfe48ffb43a2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028

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

theorem supportResidual_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

theorem extracted_residual_coprime (I J : Ideal O) (S : Finset (Ideal O)) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    intro P hP hQ
    exact (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)

theorem supportExtract_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [supportExtract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportResidual_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp only [supportResidual, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportExtract_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

theorem supportExtract_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportExtract, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

theorem supportResidual_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportResidual, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Extraction
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealRectangle_extract (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealRectangle W₁ W₂
        (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
        (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp only [idealRectangle, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  congr 2 <;> congr 1 <;> ring

end SevenEighths.CenteredMomentExtraction
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSectors
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem supportExtract_of_subset (I : Ideal O) (hI : I≠0) (S : Finset (Ideal O))
    (hS : primeSupport I⊆S) : supportExtract I S=I := by
  unfold supportExtract
  rw [Multiset.filter_eq_self.mpr (fun P hP => hS (Multiset.mem_toFinset.mpr hP))]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

end SevenEighths.CenteredMomentCommonSectors

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocation
open CenteredMomentSupport CenteredMomentCommonSectors CenteredMomentExtraction
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem extract_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportExtract (C*a) (primeSupport C)=C := by
  rw [supportExtract_mul C a hC ha,
    supportExtract_of_subset C hC _ (Finset.Subset.refl _),
    supportExtract_of_disjoint a _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa).symm,
    mul_one]

theorem residual_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportResidual (C*a) (primeSupport C)=a := by
  apply mul_left_cancel₀ hC
  have he := support_reconstruct (C*a) (mul_ne_zero hC ha) (primeSupport C)
  rwa [extract_coprime_product C a hC ha hCa] at he

theorem tuple_products {ι : Type*} [Fintype ι] (v : ι → Ideal O) (C a : Ideal O)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hv : ∏ i,v i=C*a) :
    (∏ i,supportExtract (v i) (primeSupport C))=C ∧
      (∏ i,supportResidual (v i) (primeSupport C))=a := by
  have hv0 : ∏ i,v i≠0 := hv.symm ▸ mul_ne_zero hC ha
  have hi (i : ι) : v i≠0 := Finset.prod_ne_zero_iff.mp hv0 i (Finset.mem_univ _)
  constructor
  · rw [← supportExtract_prod Finset.univ v (fun i _ => hi i),hv]
    exact extract_coprime_product C a hC ha hCa
  · rw [← supportResidual_prod Finset.univ v (fun i _ => hi i),hv]
    exact residual_coprime_product C a hC ha hCa

theorem residual_factor_coprime (C I : Ideal O) (hC : C≠0) :
    IsCoprime C (supportResidual I (primeSupport C)) := by
  have hh := extracted_residual_coprime C I (primeSupport C)
  rwa [supportExtract_of_subset C hC _ (Finset.Subset.refl _)] at hh

end SevenEighths.CenteredMomentCommonAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllocationBox
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationBox
open CenteredMomentCommonAllocation CenteredMomentSupport CenteredMomentCommonSectors
open CenteredMomentFirstSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem residualBoxes_image (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) :
    (residualBoxes S C B hB).image (fun v i => B i*v i)=sourceFiber S C B := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hui := Fintype.mem_piFinset.mp hu
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact (mem_residualPool (B i) (hB i) (S i) _).mp (Finset.mem_filter.mp (hui i)).1
    · intro i
      have hp := Finset.mem_filter.mp (hui i)
      have hsrc := (mem_residualPool (B i) (hB i) (S i) _).mp hp.1
      have hu0 : u i≠0 := right_ne_zero_of_mul (hS i _ hsrc)
      rw [supportExtract_mul _ _ (hB i) hu0,supportExtract_of_subset _ (hB i) _ (hBs i),
        supportExtract_of_disjoint _ _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hu0).mpr hp.2).symm,mul_one]
  · intro hv
    obtain ⟨hv,hvB⟩ := Finset.mem_filter.mp hv
    have hvi := Fintype.mem_piFinset.mp hv
    let u := fun i => supportResidual (v i) (primeSupport C)
    have hi (i : ι) : B i*u i=v i := by
      rw [← hvB i]
      exact support_reconstruct _ (hS i _ (hvi i)) _
    refine Finset.mem_image.mpr ⟨u,?_,funext hi⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_residualPool (B i) (hB i) (S i) _).mpr
      rw [hi]
      exact hvi i
    · exact residual_factor_coprime C (v i) hC

theorem sourceFiber_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,F v)=
      ∑ u∈residualBoxes S C B hB,F (fun i => B i*u i) := by
  rw [← residualBoxes_image S hS C hC B hB hBs,Finset.sum_image]
  intro u hu v hv he
  funext i
  exact mul_left_cancel₀ (hB i) (congrFun he i)

theorem sourceFiber_product_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (hprod : ∏ i,B i=C)
    (a : Ideal O) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)=
      ∑ u∈residualBoxes S C B hB,if (∏ i,u i)=a then F (fun i => B i*u i) else 0 := by
  rw [sourceFiber_sum S hS C hC B hB hBs]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.prod_mul_distrib,hprod,mul_right_inj' hC]

end SevenEighths.CenteredMomentCommonAllocationBox

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonAllocationSum
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocation CenteredMomentCommonAllocationBox CenteredMomentSupport
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem sum_source_fibers (S : ι → Finset (Ideal O)) (C : Ideal O)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,F v)=∑ B∈allocationLabels S C,∑ v∈sourceFiber S C B,F v := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=Fintype.piFinset S) (t:=allocationLabels S C)
    (g:=fun v i => supportExtract (v i) (primeSupport C))
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) F
  symm
  convert (preTransparency := .instances) hh using 1
  apply Finset.sum_congr rfl
  intro B hB
  congr 1
  ext v
  simp only [sourceFiber,Finset.mem_filter,funext_iff]

theorem sum_actual_allocations (S : ι → Finset (Ideal O))
    (C a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B∈actualAllocations S C,
        ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0 := by
  rw [sum_source_fibers S C]
  symm
  apply Finset.sum_filter_of_ne
  intro B hB hn
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp : (∏ i,v i)=C*a := by
    by_contra hh
    exact hne (if_neg hh)
  have he := (tuple_products v C a hC ha hCa hp).1
  have hb := (Finset.mem_filter.mp hv).2
  simpa only [hb] using he

theorem original_coefficient_allocated (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B : actualAllocations S C,
        ∑ u∈residualBoxes S C B
          (allocation_data S C B (Finset.mem_filter.mp B.property).1).1,
          if (∏ i,u i)=a then F (fun i => B.val i*u i) else 0 := by
  rw [sum_actual_allocations S C a hC ha hCa F]
  rw [← Finset.sum_coe_sort (actualAllocations S C)
    (fun B => ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)]
  apply Finset.sum_congr rfl
  intro B hB
  exact sourceFiber_product_sum S hS C hC B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).2
    (Finset.mem_filter.mp B.property).2 a F

end SevenEighths.CenteredMomentCommonAllocationSum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonProfile
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem remaining_product (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    finiteTupleProduct u=finiteTupleProduct (remainingTuple B u) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,remainingTuple,
    Sum.elim_inl,Sum.elim_inr]
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => u (Sum.inl i))]
  congr 1
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply hf i
  intro hBi
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBi⟩)

theorem slot_profiles_split (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (β : ι → Ideal O → ℂ) :
    (∏ i,β i (B (Sum.inl i)*u (Sum.inl i)))=
      (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),β i (B (Sum.inl i)))*
        ∏ i : liveIndices B,β i.val (u (Sum.inl i.val)) := by
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => β i (u (Sum.inl i)))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1)
    (fun i => β i (B (Sum.inl i)*u (Sum.inl i))),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hf i (Finset.mem_filter.mp hi).2,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem profile_common_allocation (B u : Tuple ι) (C R s : Ideal O)
    (hB : finiteTupleProduct B=C) (hsC : s∣C)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
        profileCoefficient R (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 (remainingTuple B u) := by
  have hprod : finiteTupleProduct (fun i => B i*u i)=C*finiteTupleProduct (remainingTuple B u) := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct u=_
    rw [hB,remaining_product B u hf]
  have hdiv : s∣C*finiteTupleProduct (remainingTuple B u) := dvd_mul_of_dvd_left hsC _
  unfold profileCoefficient
  rw [slot_profiles_split B u hf (fun i I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)),hprod]
  simp only [hdiv,ite_true,one_dvd,mul_one,remainingTuple_slot,remainingTuple_plain,
    IsCoprime.mul_left_iff]
  rw [mul_assoc B₁,mul_assoc B₂]
  by_cases hC : IsCoprime C R <;>
    by_cases hu : IsCoprime (finiteTupleProduct (remainingTuple B u)) R <;>
    simp_all only [true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,mul_one]
  ring

end SevenEighths.CenteredMomentCommonProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceCommonMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceCommonMask
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem profile_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hne : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (finiteTupleProduct v) R ∧ s∣finiteTupleProduct v := by
  constructor
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul])
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero])

end SevenEighths.CenteredMomentSourceCommonMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonPuncture
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPuncture
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

 theorem residualBoxes_filter {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0) :
    residualBoxes S C B hB=
      (Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i))).filter
        (fun u => IsCoprime C (∏ i,u i)) := by
  ext u
  simp only [residualBoxes,Fintype.mem_piFinset,Finset.mem_filter,
    IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  exact forall_and

theorem residualBoxes_sum {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (F : (ι → Ideal O) → ℂ) :
    (∑ u∈residualBoxes S C B hB,F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        (if IsCoprime C (∏ i,u i) then 1 else 0)*F u := by
  rw [residualBoxes_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

theorem profileCoefficient_puncture {ι : Type*} [Fintype ι]
    (C R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    (if IsCoprime C (finiteTupleProduct v) then 1 else 0)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  unfold profileCoefficient
  rw [IsCoprime.mul_right_iff,show IsCoprime C (finiteTupleProduct v) ↔ IsCoprime (finiteTupleProduct v) C from isCoprime_comm]
  by_cases hC : IsCoprime (finiteTupleProduct v) C <;>
    by_cases hR : IsCoprime (finiteTupleProduct v) R <;> simp [hC,hR]

end SevenEighths.CenteredMomentCommonPuncture

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RemainingBox
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem restore_remaining (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    restoreTuple B (remainingTuple B u)=u := by
  funext i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · rfl
    · exact (hf i (by simpa [liveIndices] using hi)).symm
  · rfl

theorem remaining_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (u : Tuple ι) (hu : u∈Fintype.piFinset S) :
    remainingTuple B u∈Fintype.piFinset (remainingSets B S) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · exact Fintype.mem_piFinset.mp hu (Sum.inl i.val)
  · exact Fintype.mem_piFinset.mp hu (Sum.inr j)

theorem restore_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (v : Tuple (liveIndices B)) (hv : v∈Fintype.piFinset (remainingSets B S)) :
    restoreTuple B v∈Fintype.piFinset S := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · exact Fintype.mem_piFinset.mp hv (Sum.inl ⟨i,hi⟩)
    · exact hg i (by simpa [liveIndices] using hi)
  · exact Fintype.mem_piFinset.mp hv (Sum.inr j)

theorem remaining_box_sum (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) := by
  apply Finset.sum_bij (fun u _ => remainingTuple B u)
  · exact fun u hu => remaining_mem B S u hu
  · intro u hu v hv he
    have hu' := restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))
    have hv' := restore_remaining B v (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hv _))
    rw [← hu',← hv',he]
  · intro v hv
    exact ⟨restoreTuple B v,restore_mem B S hg v hv,remaining_restore B v⟩
  · intro u hu
    rw [restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))]

theorem remaining_box_sum_gate (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      if (∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) else 0 := by
  split_ifs with hg
  · exact remaining_box_sum B S hf hg F
  · have he : Fintype.piFinset S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      apply hg
      intro i hi
      have hui := Fintype.mem_piFinset.mp hu (Sum.inl i)
      rwa [hf i hi _ hui] at hui
    rw [he,Finset.sum_empty]

end SevenEighths.CenteredMomentRemainingBox

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceLiveAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveAllocation
open CenteredMomentRemainingBox CenteredMomentCommonProfile CenteredMomentCommonPuncture
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem prime_residual_frozen (B : Tuple ι) (hB : ∀ i,B i≠0)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → ∀ I∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)),I=1 := by
  intro i hi I hI
  have hprime := hp i _ ((mem_residualPool _ _ _ _).mp hI)
  rcases hprime.irreducible.isUnit_or_isUnit rfl with h|h
  · exact False.elim (hi (by simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h))
  · simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h

theorem allocation_frozen_gate (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O) (B : Tuple ι)
    (hB : B∈CenteredMomentCommonAllocationSum.allocationLabels S C) :
    ∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i) := by
  classical
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hB
  intro i hi
  have hvi : v (Sum.inl i)∈S (Sum.inl i) := by
    have hh := hv
    simp only [Fintype.mem_piFinset] at hh
    exact hh (Sum.inl i)
  have he := congrFun hvB (Sum.inl i)
  change CenteredMomentSupport.supportExtract (v (Sum.inl i))
    (IdealMobiusDivisorSum.primeSupport C)=B (Sum.inl i) at he
  rw [CenteredMomentSupport.supportExtract_prime _ (hp i _ hvi)] at he
  split_ifs at he with hm
  · rwa [he] at hvi
  · exact False.elim (hi he.symm)

theorem residual_source_profile (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O)
    (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (F : Tuple (liveIndices B) → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        F (remainingTuple B u))=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
      (if (∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B (fun i => residualPool (B i) (hB i) (S i))),
          profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
            (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
            (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v else 0) := by
  let T := fun i => residualPool (B i) (hB i) (S i)
  have hf := prime_residual_frozen B hB S hp
  let A := (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0)
  let G := fun v : Tuple (liveIndices B) =>
    profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
      (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
      (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v
  rw [residualBoxes_sum]
  calc
    _ = ∑ u∈Fintype.piFinset T,A*G (remainingTuple B u) := by
      apply Finset.sum_congr
      · ext u;simp only [Fintype.mem_piFinset];rfl
      · intro u hu
        have hfu : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 :=
          fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _)
        rw [profile_common_allocation B u C R s hprod hsC hfu]
        change (if IsCoprime C (finiteTupleProduct u) then 1 else 0)*
          (A*_ * F (remainingTuple B u))=_
        rw [remaining_product B u hfu]
        dsimp only [G]
        rw [← profileCoefficient_puncture C R]
        ring
    _ = A*(∑ u∈Fintype.piFinset T,G (remainingTuple B u)) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [remaining_box_sum_gate B T hf]
      simp only [remaining_restore,T,mem_residualPool,mul_one]
      rfl

end SevenEighths.CenteredMomentSourceLiveAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveColumn
open CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceLiveColumn.instDecidableEqSumFinOfNatNat_solutions
theorem residual_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ u∈residualBoxes S C B hB,if finiteTupleProduct u=a then
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i) else 0)=
      frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B hB)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  have hh := residual_source_profile S hp B hB C R s hprod hsC ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (fun v => if finiteTupleProduct v=a then 1 else 0)
  rw [if_pos (allocation_frozen_gate S hp C B hlabel)] at hh
  calc
    _ = ∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        (if finiteTupleProduct (remainingTuple B u)=a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
        intro i hi
        have hui := hu
        simp only [residualBoxes,Fintype.mem_piFinset] at hui
        exact prime_residual_frozen B hB S hp i hi _
          (Finset.mem_filter.mp (hui (Sum.inl i))).1
      rw [remaining_product B u hf]
      split_ifs <;> simp
    _ = _ := hh.trans (by
      unfold frozenCoefficient finiteColumnCoefficient liveBox liveProfile
      rw [Finset.sum_filter]
      congr 1
      apply Finset.sum_congr
      · ext v;simp only [Fintype.mem_piFinset]
      intro v hv
      split_ifs <;> simp)

theorem original_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)=
      ∑ B : actualAllocations S C,
        frozenCoefficient B C R ν Wslot P*
          finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
            (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  simp only [finiteColumnCoefficient, Finset.sum_filter]
  have halloc := original_coefficient_allocated S hS C a hC ha hCa
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  change (∑ v ∈ Fintype.piFinset S, if finiteTupleProduct v = C * a then
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v else 0) = _ at halloc
  rw [halloc]
  apply Finset.sum_congr rfl
  intro B hB
  have h := residual_source_column S hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s a
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2 hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp only [finiteColumnCoefficient, Finset.sum_filter] at h
  exact h

end SevenEighths.CenteredMomentSourceLiveColumn

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LiveSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentLiveSupport
open CenteredMomentSourceLiveColumn CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentFirstSectors CenteredMomentSourceCommonMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentLiveSupport.instDecidableEqSumFinOfNatNat_definitions
theorem restore_frozen (B : Tuple ι) (v : Tuple (liveIndices B)) :
    ∀ i,B (Sum.inl i)≠1 → restoreTuple B v (Sum.inl i)=1 := by
  intro i hi
  simp only [restoreTuple,Sum.elim_inl]
  rw [dif_neg (by simpa [liveIndices] using hi)]

theorem restore_product (B : Tuple ι) (v : Tuple (liveIndices B)) :
    finiteTupleProduct (restoreTuple B v)=finiteTupleProduct v := by
  rw [remaining_product B _ (restore_frozen B v),remaining_restore]

theorem restored_original_mem (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (hlabel : B∈allocationLabels S C)
    (v : Tuple (liveIndices B)) (hv : v∈liveBox S B hB) :
    (fun i => B i*restoreTuple B v i)∈Fintype.piFinset S := by
  have hg : ∀ i,B (Sum.inl i)≠1 →
      (1:Ideal O)∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)) := by
    intro i hi
    rw [mem_residualPool,mul_one]
    exact allocation_frozen_gate S hp C B hlabel i hi
  have hu := restore_mem B (fun i => residualPool (B i) (hB i) (S i)) hg v (by simpa only [liveBox,Fintype.mem_piFinset] using hv)
  apply Fintype.mem_piFinset.mpr
  intro i
  simp only [Fintype.mem_piFinset] at hu
  exact (mem_residualPool _ _ _ _).mp (hu i)

theorem live_column_original_support (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (hne : finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a≠0) :
    C*a∈finiteColumns (Fintype.piFinset S) ∧ a≠0 ∧ IsCoprime C a := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
  have hm := profile_nonzero_masks (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v hvn
  rw [ha,IsCoprime.mul_right_iff] at hm
  have hsrc := restored_original_mem S hp C B hB hlabel v hv
  have he : finiteTupleProduct (fun i => B i*restoreTuple B v i)=C*a := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct (restoreTuple B v)=_
    rw [hprod,restore_product,ha]
  have hn : C*a≠0 := by
    rw [← he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hS i _ (Fintype.mem_piFinset.mp hsrc i))
  exact ⟨Finset.mem_image.mpr ⟨_,hsrc,he⟩,right_ne_zero_of_mul hn,hm.1.2.symm⟩

end SevenEighths.CenteredMomentLiveSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_split (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

end SevenEighths.CenteredMomentSourceRow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LiveDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentLiveDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem finite_column_mem {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (a : Ideal O) (ha : finiteColumnCoefficient S β a≠0) : a∈finiteColumns S := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_image.mpr ⟨v,hv,he⟩

 theorem sum_same_support (S T : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (hST : ∀ I∈S,c I≠0 → I∈T) (hTS : ∀ I∈T,c I≠0 → I∈S) :
    (∑ I∈S,c I*f I)=∑ I∈T,c I*f I := by
  have hs : (∑ I∈S∩T,c I*f I)=∑ I∈S,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hI,hST I hI h⟩)
    rw [hc,zero_mul]
  have ht : (∑ I∈S∩T,c I*f I)=∑ I∈T,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hTS I hI h,hI⟩)
    rw [hc,zero_mul]
  exact hs.symm.trans ht

variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentLiveDomain.instDecidableEqSumFinOfNatNat_solutions
theorem live_column_sum (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    (∑ I∈supportedColumns (residualPool C hC.1 (finiteColumns (Fintype.piFinset S))),c I*f I)=
      ∑ I∈supportedColumns (finiteColumns (liveBox S B hB)),c I*f I := by
  dsimp only
  apply sum_same_support
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨finite_column_mem _ _ I hn,(Finset.mem_filter.mp hI).2⟩
  · intro I hI hn
    have hh := live_column_original_support S hS hp B hB C R I hlabel hprod
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact Finset.mem_filter.mpr ⟨(mem_residualPool C hC.1 _ I).mpr hh.1,(Finset.mem_filter.mp hI).2⟩

end SevenEighths.CenteredMomentLiveDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentOriginalChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentOriginalChildEnergy.instDecidableEqSumFinOfNatNat_solutions
theorem original_source_punctured_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  by_cases hc : IsCoprime C I
  · rw [if_pos hc]
    exact original_source_column S hS hp C R s I hC hI hc hsC ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂
  · rw [if_neg hc]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    have hz : finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=0 := by
      by_contra hn
      exact hc (live_column_original_support S hS hp B
        (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R I
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn).2.2
    rw [hz,mul_zero]

end SevenEighths.CenteredMomentOriginalChildEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationLiveMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLiveMask
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentOriginalChildEnergy CenteredMomentRemainingBox CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationLiveMask.instDecidableEqSumFinOfNatNat_definitions
theorem profile_mask (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*
        (if s∣finiteTupleProduct v then 1 else 0) := by
  simp only [profileCoefficient,one_dvd,ite_true,mul_one]

theorem column_mask (S : Finset (Tuple ι)) (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O) :
    finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I=
      finiteColumnCoefficient S
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1) I*
          (if s∣I then 1 else 0) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [profile_mask,(Finset.mem_filter.mp hv).2]

end SevenEighths.CenteredMomentAmplificationLiveMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRawScale
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem plainNorm_pos (B : Tuple ι) (hB : ∀ i,B i≠0) : 0<plainNorm B := by
  unfold plainNorm
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB _))

omit [Fintype ι] in
theorem frozenScale_pos (B : Tuple ι) (P : ι → ℝ) (hP : ∀ i,0<P i) (i : ι) :
    0<frozenScale B P i := by
  unfold frozenScale
  split_ifs
  · exact zero_lt_one
  · exact hP i

theorem rawReduction_pos (B : Tuple ι) (hB : ∀ i,B i≠0) (P : ι → ℝ) (hP : ∀ i,0<P i) :
    0< rawReduction B P := mul_pos (plainNorm_pos B hB) (Finset.prod_pos (fun i _ => frozenScale_pos B P hP i))

theorem slot_scale_split (B : Tuple ι) (P : ι → ℝ) :
    (∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)=∏ i,P i := by
  rw [Finset.prod_coe_sort (liveIndices B) P]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1) P]
  unfold frozenScale liveIndices
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  ring

theorem raw_scale_identity (B : Tuple ι) (hB : ∀ i,B i≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B T P*rawReduction B P=T*∏ i,P i := by
  unfold remainingRaw rawReduction
  have h := slot_scale_split B P
  calc
    _ = T*((∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)) := by
      field_simp [(plainNorm_pos B hB).ne']
    _ = _ := by rw [h]

end SevenEighths.CenteredMomentCommonRawScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RestrictedDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem source_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*CanonicalRowCompletion.idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*CanonicalRowCompletion.idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]

variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentRestrictedDomain.instDecidableEqSumFinOfNatNat_definitions
theorem live_rowPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    rowPolynomial Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q => c I*f I) z=
      rowPolynomial Finset.univ (sourceGenerator T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_rowPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_rowPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*CanonicalRowCompletion.idealRowHom z I)

end SevenEighths.CenteredMomentRestrictedDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RestrictedSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem rowPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    rowPolynomial S a (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*rowPolynomial S a (d B) z := by
  simp only [rowPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentRestrictedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [if_pos hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

end SevenEighths.CenteredMomentSecondHeightFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangle
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangle
open ActualEisensteinCubic HeckeFamily CenteredMomentHeckeExpansion CenteredMomentRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentExtraction CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentRemainingBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem pack_product (v : ι→Ideal O) (I J : Ideal O) :
    finiteTupleProduct (pack v I J)=(∏ i,v i)*I*J := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,pack_slot,Fin.prod_univ_two,
    pack_left,pack_right,mul_assoc]

theorem sum_tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (f : Tuple ι→ℂ) :
    (∑ v∈tuplePool slots S₁ S₂,f v)=
      ∑ v : (∀ i,slots i),∑ I : S₁,∑ J : S₂,f (pack (fun i=>v i) I J) := by
  rw [← Finset.sum_coe_sort (tuplePool slots S₁ S₂) f]
  have he := (tuplePoolEquiv slots S₁ S₂).symm.sum_comp (fun v : tuplePool slots S₁ S₂=>f v)
  change (∑ x : ((∀ i,slots i)×S₁×S₂),f (pack (fun i=>x.1 i) x.2.1 x.2.2))=
    (∑ v : tuplePool slots S₁ S₂,f v) at he
  simpa only [Fintype.sum_prod_type] using he.symm

theorem finite_column_regroup (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (w : Ideal O→ℂ) :
    (∑ I∈finiteColumns S,finiteColumnCoefficient S β I*w I)=
      ∑ v∈S,β v*w (finiteTupleProduct v) := by
  simp only [finiteColumnCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I∈finiteColumns S,∑ v∈S.filter (fun v=>finiteTupleProduct v=I),
        β v*w (finiteTupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

theorem rectangle_zero_left (S₁ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (I J : Ideal O) (hI : I∉S₁) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₁ ((Ideal.absNorm (B₁*I):ℝ)/X₁)=0 := by
    by_contra hn;exact hI (h I (Or.inl hn))
  have hy : W₁ ((Ideal.absNorm (B₁*I):ℝ)/Y₁)=0 := by
    by_contra hn;exact hI (h I (Or.inr hn))
  simp only [idealRectangle,hx,hy,zero_mul,sub_self]

theorem rectangle_zero_right (S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₂ W₂ B₂ X₂ Y₂) (I J : Ideal O) (hJ : J∉S₂) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₂ ((Ideal.absNorm (B₂*J):ℝ)/X₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inl hn))
  have hy : W₂ ((Ideal.absNorm (B₂*J):ℝ)/Y₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inr hn))
  simp only [idealRectangle,hx,hy,mul_zero,sub_self]

theorem finite_plain_rectangle (S₁ S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (f : Ideal O→Ideal O→ℂ) :
    (∑ I : S₁,∑ J : S₂,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))=
      ∑' I : Ideal O,∑' J : Ideal O,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) := by
  symm
  rw [tsum_eq_sum (s := S₁)]
  · rw [← Finset.sum_coe_sort S₁ (fun I=>∑' J : Ideal O,
      f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))]
    apply Finset.sum_congr rfl
    intro I hI
    rw [tsum_eq_sum (s := S₂)]
    · exact (Finset.sum_coe_sort S₂ _).symm
    · intro J hJ
      rw [rectangle_zero_right S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₂ I J hJ,mul_zero]
  · intro I hI
    simp only [rectangle_zero_left S₁ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ I _ hI,mul_zero,tsum_zero]

theorem source_polynomial_eq_full_masked_rectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [finite_column_regroup,sum_tuplePool]
  unfold fullMaskedRectangle
  apply Finset.sum_congr rfl
  intro v hv
  rw [← finite_plain_rectangle S₁ S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ h₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [profileCoefficient,pack_product,pack_slot,pack_left,pack_right]
  ring

theorem liveBox_eq_tuplePool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ i,B i≠0) :
    liveBox S B hB = tuplePool
      (fun i : liveIndices B=>residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val)))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  ext v
  simp only [liveBox,tuplePool,Fintype.mem_piFinset]
  constructor <;> intro h i
  all_goals
    cases i with
    | inl i => exact h (Sum.inl i)
    | inr j =>
      fin_cases j
      · exact h (Sum.inr 0)
      · exact h (Sum.inr 1)

end SevenEighths.CenteredMomentSourceRectangle

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRectangleMask
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSourceRectangle
open CenteredMomentDivisorRowEnergy CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_ideal_mask (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (R I : Ideal O) :
    (if IsCoprime I R then (1:ℂ) else 0)*rowWeight η m A z t I=
      rowWeight η (m*idealGenerator R) A z t I := by
  by_cases hI : Supported I
  · have hm : (m*idealGenerator R)^6*(A*z)=(idealGenerator R)^6*(m^6*(A*z)) := by ring
    change (if IsCoprime I R then (1:ℂ) else 0)*
      ((idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))=
      (idealCoeff η I*idealRowHom ((m*idealGenerator R)^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)
    rw [hm,idealRowHom_argument_mul ((idealGenerator R)^6) (m^6*(A*z)) I,
      idealRowHom_sixth_mask (idealGenerator R) I hI,span_idealGenerator]
    ring
  · rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hI,
      rowWeight_zero_of_not_supported η (m*idealGenerator R) A z t
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) I hI,mul_zero]

theorem fullMaskedRectangle_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  unfold fullMaskedRectangle maskedRectangle
  apply Finset.sum_congr (by ext;simp)
  intro v hv
  congr 1
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [idealRectangle_extract]
  rw [mul_right_comm (if IsCoprime _ R then (1:ℂ) else 0) _,rowWeight_ideal_mask η m A z t hmLam hm2]
  ring

theorem source_polynomial_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈CenteredMomentSourceMass.finiteColumns (tuplePool slots S₁ S₂),
      CenteredMomentSourceMass.finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (CenteredMomentSourceProfileMass.profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ R L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_eq_maskedRectangle η m A z t hmLam hm2 slots ν _ R L W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂)

end SevenEighths.CenteredMomentSourceRectangleMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangleEnergy
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
local notation "O" => ActualEisensteinCubic.O

theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])

end SevenEighths.CenteredMomentSourceRectangleEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CanonicalRetainedSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalRetainedSource
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem live_residual_pool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

omit [DecidableEq ι] in
theorem liveBox_original_pools (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) :
    liveBox S B hB=tuplePool (fun i:liveIndices B=>S (Sum.inl i.val))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  rw [liveBox_eq_tuplePool]
  simp_rw [live_residual_pool]

end SevenEighths.CenteredMomentCanonicalRetainedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRadialData
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma Input.pools_ne (s:Input ι) (j:ι⊕Fin 2) : ∀I∈s.pools j,I≠0 := by
  cases j with
  | inl i => exact fun I hI=>(s.prime i I hI).ne_zero
  | inr j =>
    fin_cases j
    · simpa [Input.pools] using s.plain₁_ne
    · simpa [Input.pools] using s.plain₂_ne

end SevenEighths.CenteredMomentCommonRadialData

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedDomain
open CenteredMomentAmplificationLiveMask CenteredMomentExceptionalMaskedSource
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentCommonLinearSource.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
theorem source_column_allocation (s:Input ι)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(hseed:seed∣C)(z:O):
    sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P*
        liveColumn s C R L B z:=by
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let b:=fun B:actualAllocations s.pools C=>frozenCoefficient B.val C R s.ν s.W s.P
  let d:=fun (B:actualAllocations s.pools C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
      (liveProfile B.val C R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
      ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff s.η s.t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
        finiteColumnCoefficient (Fintype.piFinset s.pools)
          (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I)
          else 0)*heightCoeff s.η s.t I=∑B,b B*d B I:=by
    have hc:=original_source_punctured_column s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
      C R seed I hC.1 (Finset.mem_filter.mp I.property).2.1 hseed
      s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  change rowPolynomial Finset.univ (sourceGenerator Q) _ z=_
  rw [funext he,rowPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=live_rowPolynomial s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
    B.val (alloc_ne s C B) C R hC (Finset.mem_filter.mp B.property).1
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    (fun I=>(if L∣I then 1 else 0)*heightCoeff s.η s.t I) z
  change rowPolynomial Finset.univ (sourceGenerator Q) (d B) z=_ at hh
  rw [hh]
  unfold liveColumn
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem live_column_rectangle (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):
    liveColumn s C R L B z=
      CenteredMomentDivisorRowEnergy.maskedRectangle
        (commonData s C R B).η (commonData s C R B).m (commonData s C R B).A z
        (commonData s C R B).t (commonData s C R B).slots (commonData s C R B).coefficient L
        (commonData s C R B).W₁ (commonData s C R B).W₂
        (commonData s C R B).X₁ (commonData s C R B).X₂
        (commonData s C R B).Y₁ (commonData s C R B).Y₂:=by
  unfold liveColumn
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hc₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hc₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hc₁ hc₂
  have he:=CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    (commonData s C R B).slots
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (commonData s C R B).ν (commonData s C R B).W (commonData s C R B).P
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) hc₁ hc₂
  rw [height_source_row]
  convert (preTransparency := .instances) he using 1 <;> simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  all_goals rfl

end SevenEighths.CenteredMomentCommonLinearSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonLinearNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearNormalization
open HeckeFamily CenteredMomentCommonLinearSource CenteredMomentCommonRadialData
open CenteredMomentCommonRawScale CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_volume (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    volume (commonData s C R B)=remainingRaw B.val (s.X₁*s.X₂) s.P:=by
  dsimp only [volume,commonData,remainingRaw,plainNorm]
  ring

theorem source_normalized (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,commonScalar s C R B*maskedAmplitude (commonData s C R B) L z:=by
  rw [source_column_allocation s C hC R seed L hseed z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [live_column_rectangle]
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  unfold commonScalar maskedAmplitude
  change (Real.sqrt (volume s.toData):ℂ)⁻¹*(_*_) =
    ((Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*_)*
      ((Real.sqrt (volume (commonData s C R B)):ℂ)⁻¹*_)
  rw [hs,Complex.ofReal_mul,mul_inv_rev]
  ring

end SevenEighths.CenteredMomentCommonLinearNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonPairedSource
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonPairedSource
open HeckeFamily UniqueFactorizationMonoid CanonicalQuadraticSieve
open CenteredMomentCommonLinearSource CenteredMomentCommonLinearNormalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem norm_column (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    ‖normalizedColumn s C hC R seed L z‖≤
      ∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖:=by
  unfold normalizedColumn
  rw [source_normalized s C hC R seed L hseed]
  simpa only [norm_mul] using norm_sum_le
    (Finset.univ:Finset (actualAllocations s.pools C))
    (fun B=>commonScalar s C R B*maskedAmplitude (commonData s C R B) L z)

theorem paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed L:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(rows:Finset O):
    (∑z∈rows,‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑z∈rows,(∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖)*
      (∑E:actualAllocations v.pools D,‖commonScalar v D R E‖*
        ‖maskedAmplitude (commonData v D R E) L z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (norm_column s C hC R seed L hsC z)
        (norm_column v D hD R seed L hsD z) (norm_nonneg _)
        (Finset.sum_nonneg (fun B _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=Finset.univ)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro z hz
      ring

theorem whole_paired_columns_oai (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
            ‖maskedAmplitude (commonData s C R B) L z‖*
              ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑L∈Ds,‖(moebius L:ℂ)‖*
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=
      Finset.sum_le_sum (fun L hL=>mul_le_mul_of_nonneg_left
        (paired_columns s v C D hC hD R seed L hsC hsD rows) (norm_nonneg _))
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro L hL
      apply Finset.sum_congr rfl
      intro z hz
      ring

end SevenEighths.CenteredMomentCommonPairedSource

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.CenteredMomentCommonPairedSource.whole_paired_columns_oai.{u_1, u_2} := @OAI.SevenEighths.CenteredMomentCommonPairedSource.whole_paired_columns_oai.{u_1, u_2}
