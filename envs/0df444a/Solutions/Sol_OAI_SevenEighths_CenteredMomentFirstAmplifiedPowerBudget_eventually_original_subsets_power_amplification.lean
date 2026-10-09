-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstAmplifiedPowerBudget.eventually_original_subsets_power_amplification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:56:10.749543+00:00
-- url     : https://prove2.me/submissions/64978218-14ff-4964-850d-7bbcc6399b5b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstAmplificationChoice_eventually_dyadic_amplification
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstAnnularAmplification_eventually_annular_amplification_common

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSupport IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentCommonSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 local instance instDecidableEqSumFinOfNatNat_solutions_rb4d21f_1 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
theorem allocation_slot_one (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (i : ι) : B.val (Sum.inl i)=1 := by
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp (Finset.mem_filter.mp B.property).1
  have hi := Fintype.mem_piFinset.mp hv (Sum.inl i)
  have hd := hslot i (v (Sum.inl i)) hi
  have he := congrFun hvB (Sum.inl i)
  have hc : IsCoprime (P^k) (v (Sum.inl i)) := hd.2.pow_left
  have hh := supportExtract_of_disjoint (v (Sum.inl i)) (primeSupport (P^k))
    ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff (pow_ne_zero k hP) hd.1).mpr hc).symm
  exact he.symm.trans hh

 theorem allocation_plain_product (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : B.val (Sum.inr 0)*B.val (Sum.inr 1)=P^k := by
  have he := (Finset.mem_filter.mp B.property).2
  rw [Fintype.prod_sum_type,show (∏ i : ι,B.val (Sum.inl i))=1 by
    simp only [allocation_slot_one S P hP k hslot B,Finset.prod_const_one],one_mul,
    Fin.prod_univ_two] at he
  exact he

 theorem allocation_plain_injective (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    Function.Injective (fun B : actualAllocations S (P^k) => B.val (Sum.inr 0)) := by
  intro B D he
  have hb := allocation_plain_product S P hP k hslot B
  have hd := allocation_plain_product S P hP k hslot D
  have hb0 := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1 (Sum.inr 0)
  have he1 : B.val (Sum.inr 1)=D.val (Sum.inr 1) := by
    apply mul_left_cancel₀ hb0
    exact (hb.trans hd.symm).trans (congrArg (fun x => x*D.val (Sum.inr 1)) he.symm)
  apply Subtype.ext
  funext i
  cases i with
  | inl i => rw [allocation_slot_one S P hP k hslot B,allocation_slot_one S P hP k hslot D]
  | inr i => fin_cases i <;> assumption

 theorem idealDivisors_prime_power_card (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (idealDivisors (P^k)).card≤k+1 := by
  have hs : idealDivisors (P^k)⊆(Finset.range (k+1)).image (fun j => P^j) := by
    intro I hI
    obtain ⟨j,hj,he⟩ := (dvd_prime_pow hP k).mp ((mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mp hI)
    have heq : I=P^j := dvd_antisymm he.dvd he.symm.dvd
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),heq.symm⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (Finset.card_range (k+1)))

theorem actual_amplification_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤k+1 := by
  let f : actualAllocations S (P^k) → idealDivisors (P^k) := fun B =>
    ⟨B.val (Sum.inr 0),(mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mpr
      ⟨B.val (Sum.inr 1),(allocation_plain_product S P hP.ne_zero k hslot B).symm⟩⟩
  have hf : Function.Injective f := by
    intro B D he
    exact allocation_plain_injective S P hP.ne_zero k hslot (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hh
  exact hh.trans (idealDivisors_prime_power_card P hP k)

end SevenEighths.CenteredMomentAmplificationAllocationCost

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationScale
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem all_slots_live (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : liveIndices (B : Tuple ι)=Finset.univ := by
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact allocation_slot_one S P hP k hslot B i

 theorem rawReduction_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) :
    rawReduction B scale=(Ideal.absNorm P:ℝ)^k := by
  unfold rawReduction plainNorm frozenScale
  simp only [allocation_slot_one S P hP k hslot B,ite_true,Finset.prod_const_one,mul_one]
  rw [← Nat.cast_mul,← map_mul,allocation_plain_product S P hP k hslot B,map_pow,Nat.cast_pow]

theorem remainingRaw_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) (Traw : ℝ) :
    remainingRaw B Traw scale=(Traw*∏ i,scale i)/(Ideal.absNorm P:ℝ)^k := by
  have hb := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1
  have he := raw_scale_identity B hb Traw scale
  rw [rawReduction_exact S P hP k hslot B scale] at he
  have hn : (Ideal.absNorm P:ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hP
  exact (eq_div_iff (pow_ne_zero k hn)).mpr he

end SevenEighths.CenteredMomentAmplificationAllocationScale

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.GaussNormalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentGaussNormalization
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentDivisorRawEnergy CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem gaussPolynomial_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => d*c i) z=d*gaussPolynomial S a ha c z := by
  simp only [gaussPolynomial,Finset.mul_sum,mul_assoc]

theorem gaussEnergy_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy S a ha (fun i => d*c i) W K=((‖d‖^2:ℝ):ℂ)*gaussEnergy S a ha c W K := by
  simp only [gaussEnergy,gaussPolynomial_const_mul,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,tsum_mul_left]

theorem gaussEnergy_central {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (gaussEnergy S a ha (fun i => (Real.sqrt T:ℂ)⁻¹*c i) W K).re=
      (gaussEnergy S a ha c W K).re/T := by
  rw [gaussEnergy_const_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hT.le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,div_eq_mul_inv,mul_comm]

end SevenEighths.CenteredMomentGaussNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem localErrorCost_nonneg (p : O) (n : ℕ) : 0≤localErrorCost p n := by
  unfold localErrorCost
  split_ifs <;> positivity

end SevenEighths.CenteredMomentAmplificationErrorEnergy

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
open CenteredMomentSourceRow CenteredMomentGaussNormalization
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationAllocationScale
open CenteredMomentHeckeColumnWindow CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationShortening
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationChildInput.instDecidableEq_solutions
theorem residual_one (S : Finset (Ideal O)) (h : (1:Ideal O)≠0) :
    residualPool 1 h S=S := by
  ext I
  simp only [mem_residualPool,one_mul]

theorem live_slot_one (B : Tuple ι) (i : liveIndices B) : B (Sum.inl i.val)=1 :=
  (Finset.mem_filter.mp i.property).2

theorem child_tuplePool (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 =
      Fintype.piFinset (child s C R B τ t).pools := by
  ext v
  simp only [liveBox,Fintype.mem_piFinset]
  constructor <;> intro h j
  all_goals
    cases j with
    | inl i =>
      have hi:=h (Sum.inl i)
      simpa only [remainingSets,child,commonData,Input.pools,Sum.elim_inl,live_slot_one B.val i,
        residual_one] using hi
    | inr j =>
      fin_cases j
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 0)
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 1)

theorem child_profile (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 = (original (child s C R B τ t) (R*C) seed).profile := by
  funext v
  simp only [maskedLiveProfile,OriginalData.profile,original,child,commonData,
    profileCoefficient,one_mul,idealRectangle_extract]
  rfl

theorem prime_slots_live (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : liveIndices B.val=Finset.univ :=
  all_slots_live s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem child_volume (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    volume (child s (Q^k) R B τ t)=volume s/(Q.absNorm:ℝ)^k := by
  change (s.X₁/(B.val (Sum.inr 0)).absNorm)*(s.X₂/(B.val (Sum.inr 1)).absNorm)*
    (∏i:liveIndices B.val,s.P i.val)=_
  rw [div_mul_div_comm]
  exact remainingRaw_exact s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B s.P (s.X₁*s.X₂)

theorem child_columns (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)=
      (original (child s C R B τ t) (R*C) seed).columns ∧
    finiteColumnCoefficient
      (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=
      (original (child s C R B τ t) (R*C) seed).beta := by
  dsimp only [OriginalData.columns, OriginalData.beta, original]
  rw [child_tuplePool s C R B τ t,child_profile s C R seed B τ t]
  dsimp only [original]
  constructor
  · apply congrArg finiteColumns
    ext v
    simp only [Fintype.mem_piFinset]
  · apply congrArg (fun S => finiteColumnCoefficient S _)
    ext v
    simp only [Fintype.mem_piFinset]

theorem child_gauss_source (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy
      (finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff τ t) W K=
    sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta
      (heightCoeff (child s C R B τ t).η (child s C R B τ t).t) W K := by
  obtain ⟨hcols,hcoeff⟩ := child_columns s C R seed B τ t
  rw [hcols,hcoeff]
  rfl

theorem original_childEnergy_eq_inputs (s : Input ι) (R seed : Ideal O)
    (τ : RayCharacter→Character) (p : O) (hp : p≠0)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime (Ideal.span {p}) I)
    (n : ℕ) (t K : ℝ) :
    (original s R seed).childEnergy τ p n t (volume s) K=
      (16*(n+2:ℝ)*localErrorCost p n)*
        ∑χ:RayCharacter,∑B:actualAllocations s.pools ((Ideal.span {p})^(n+1)),
          childNormalizedGaussSource s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K := by
  have hQ : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  unfold OriginalData.childEnergy
  simp only [original,Finset.sum_div]
  apply congrArg (fun x : ℝ => (16*(n+2:ℝ)*localErrorCost p n)*x)
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro B hB
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_volume s (Ideal.span {p}) hQ (n+1) hslot R B (τ χ) t,
    child_gauss_source s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K]

end SevenEighths.CenteredMomentAmplificationChildInput

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularInput
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum

variable {ι:Type*}[Fintype ι]

theorem normalized_input_coefficient (s:Input ι)(R seed:Ideal HeckeFamily.O)
    (W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold OriginalData.coefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily

variable {ι:Type*}[Fintype ι]

lemma original_active (s:Input ι)(R seed:Ideal HeckeFamily.O):
    original (activeInput s) R seed=(original s R seed).active:=by
  unfold original OriginalData.active
  congr 1
  funext j
  cases j <;> rfl

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

local instance instDecidableEqSumFinOfNatNat_solutions_rb4d21f_2 {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
theorem eventually_input_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                normalizedGaussSource s R seed ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)+
                ∑p : elementPool P,∑i : Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
                    ∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools
                        ((Ideal.span {p.val})^(errorIndex i+1)),
                      childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                        R seed B (τ p i χ) s.t ballProfile
                        (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                          (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
    hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _)
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have he:=henergy (original s R seed) s.pools_ne s.prime hsupp z hz hlen hR0 hs0 hR hs
    s.t (volume s) d cLog (volume_pos s) I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  rw [←hsη,normalized_input_coefficient,normalized_input_coefficient] at he
  convert (preTransparency := .instances) he using 1
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
    (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
  have hcop:∀i,∀Q∈(activeInput s).slots i,IsCoprime (Ideal.span {p.val}) Q:=by
    exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
      hsupp (original s R seed).active_slot
      (fun i Q hQ=>s.prime i Q ((original s R seed).active_subset _ hQ))
      (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  apply Finset.sum_congr rfl
  intro i _
  rw [←original_active]
  exact (original_childEnergy_eq_inputs (activeInput s) R seed (τ p i) p.val hd.1.ne_zero hcop
    (errorIndex i) s.t _).symm

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstErrorAllocationPower
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstErrorAllocationPower
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildProfileControl
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEq_solutions_rb4d21f_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
lemma child_mass_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    mass (child s (Q^k) R B τ t)=mass s := by
  change (∏i:liveIndices B.val,s.M i.val)=∏i,s.M i
  rw [Finset.prod_coe_sort,prime_slots_live s Q hQ k hslot B]

lemma allocations_card (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) :
    Fintype.card (actualAllocations s.pools (Q^k))≤k+1 := by
  simpa only [Fintype.card_coe] using actual_amplification_allocations_card s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩)

theorem budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  simp_rw [child_volume s Q hQ.ne_zero k hslot,child_mass_eq s Q hQ.ne_zero k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hs : 0≤∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j) :=
    Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _))
  have hc : (Fintype.card (actualAllocations s.pools (Q^k)):ℝ)≤k+1 := by
    exact_mod_cast allocations_card s Q hQ k hslot
  calc
    _≤((k:ℝ)+1)*((∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hs (sq_nonneg _))
    _=_ := by push_cast;ring

end SevenEighths.CenteredMomentFirstErrorAllocationPower

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAmplifiedPowerBudget
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

open CenteredMomentFirstAnnularInput CenteredMomentFirstErrorAllocationPower
local instance instDecidableEqSumFinOfNatNat_solutions_rb4d21f_3 {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
theorem eventually_input_power_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec
    H0 hH0 houter hcap amain aerror α haerr hmain herr
  have he:=henergy s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec
    hK hX hsec H0 hH0 houter hcap
  apply he.trans
  have hpweight:0≤56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ):=by positivity
  have hmweight:0≤(Mmax+2*sigma)/(sigma/6):=by positivity
  have herror: ∀p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∀i:Fin 3,
      (∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          R seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
            (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1)))≤
      (errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
        (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
          CenteredMomentFirstChildProfileControl.mass s^2:=by
    intro p i
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
    have hcop:∀j,∀Q∈(activeInput s).slots j,IsCoprime (Ideal.span {p.val}) Q:=by
      exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
        hsupp (original s R seed).active_slot
        (fun j Q hQ=>s.prime j Q ((original s R seed).active_subset _ hQ))
        (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hq:Prime (Ideal.span {p.val}):=(hdata _ hd.2.1).1
    calc
      _≤∑χ:RayCharacter,((errorIndex i+1+1:ℕ):ℝ)*
          (∑j,aerror p i χ j*(volume (activeInput s)/
            ((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
              CenteredMomentFirstChildProfileControl.mass (activeInput s)^2:=by
        apply Finset.sum_le_sum
        intro χ hχ
        apply le_trans (Finset.sum_le_sum (fun B _=>herr p i χ B))
        exact budget_sum_le (activeInput s) (Ideal.span {p.val}) hq (errorIndex i+1) hcop R
          (fun _=>τ p i χ) (fun _=>s.t) 4 (aerror p i χ) α (haerr p i χ)
      _=_:=by
        simp only [CenteredMomentFirstChildProfileControl.mass,activeInput]
        push_cast
        rw [←Finset.sum_mul,←Finset.mul_sum]
        congr 2
        ring
  calc
    _≤(56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          ((∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)+
          ∑p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
            ((errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
              (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
                CenteredMomentFirstChildProfileControl.mass s^2)):=by
      apply mul_le_mul_of_nonneg_left _ hpweight
      apply add_le_add (mul_le_mul_of_nonneg_left hmain hmweight)
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (herror p i)
        (mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i)))
    _=_:=by
      simp only [←mul_assoc,←Finset.sum_mul]
      ring

theorem eventually_original_subsets_power_amplification_oai {Ω : Type*} [Fintype Ω]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (A:Finset Ω) → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (A:Finset Ω) (p : elementPool P) i χ,(τ A p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ A:Finset Ω,∀ s : Input A,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : A→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ A p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  have hall:=Filter.eventually_all.mpr (fun A:Finset Ω=>
    eventually_input_power_amplification (ι:=A) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
      hsigma hloss hM hb hgap hC hxi hreserve)
  filter_upwards [hall] with Z hz
  have hbase:=hz (∅:Finset Ω)
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.1,?_⟩
  intro η
  have hf (A:Finset Ω):=(hz A).2.2.2 η
  choose τ hN he using hf
  exact ⟨τ,hN,he⟩

end SevenEighths.CenteredMomentFirstAmplifiedPowerBudget

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentFirstAmplifiedPowerBudget.eventually_original_subsets_power_amplification_oai.{u_1} := @OAI.SevenEighths.CenteredMomentFirstAmplifiedPowerBudget.eventually_original_subsets_power_amplification_oai.{u_1}
