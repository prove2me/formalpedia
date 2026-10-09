-- Prove2me | solution 3 for OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers.actual_low_homogeneous_four_powers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:34:38.376983+00:00
-- url     : https://prove2.me/submissions/d111e8f7-7e7b-4505-a61a-03c61ba95ec9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
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

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
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

theorem residualPart_self (I : Ideal O) : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self (I : Ideal O) (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm

end SevenEighths.CenteredMomentCompleteCommon

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

theorem elementPool_card (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes) :
    (elementPool P).card = P.card := by
  apply Finset.card_image_of_injOn
  intro Q hQ R hR he
  rw [← (primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1,
    ← (primaryPrime_data R (hp R hR) (hbad R hR)).2.1,he]

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

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

end SevenEighths.CenteredMomentSectorLocalization

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
theorem canonical_active_log_le (η τ : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}) :
    0≤Real.logb Z (τ.modulus.absNorm:ℝ) ∧
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)≤
      Real.logb Z (τ.modulus.absNorm:ℝ) := by
  have hpos : 0<τ.modulus.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hd : Ideal.span {activeConductor I J}∣τ.modulus := by
    rw [hmod,←Ideal.span_singleton_mul_span_singleton]
    exact (dvd_mul_left (Ideal.span {activeConductor I J}) _).trans (dvd_mul_left _ _)
  have hN : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)
  refine ⟨Real.logb_nonneg hZ (by exact_mod_cast hpos),?_⟩
  exact Real.logb_le_logb_of_le hZ (active_norm_pos I J) hN

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

theorem errorRemoval_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z) (k : ℕ) :
    Z^(errorRemoval p Z k)=(normValue p)^k := by
  unfold errorRemoval
  rw [mul_comm,Real.rpow_mul_natCast (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)]

end SevenEighths.CenteredMomentFirstAmplificationChoice

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

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedAllowance
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical
open CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales
local notation "O"=>ActualEisensteinCubic.O

lemma allowance_nonneg (C D:Ideal O)(Z:ℝ):0≤allowance C D Z:=by
  unfold allowance;positivity

end SevenEighths.CenteredMomentFirstMixedAllowance

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonRadiusSaving
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadiusSaving
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem common_saving_identity (c d x w q wo B sigma branch delta reserve ell : ℝ) :
    firstSaving c (d+x) w q wo B
      (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell =
      c/6+5*d/6+w/3+q/6+wo+B-5*max (d-c-2*w+wo) 0/6-
        5*branch*sigma/6-5*(delta+reserve)/6+ell := by
  unfold firstSaving
  ring

theorem common_saving_lower (c d x w q wo B sigma branch delta reserve ell : ℝ)
    (hc : 0≤ c) (hw : 0≤w) (hq : 0≤q) (hwo : 0≤wo) (hB : 0≤B)
    (hallow : 3*c-5*d≤6*B+q) :
    2*(c+w)/3-max (w/3-wo) 0-5*branch*sigma/6-5*(delta+reserve)/6+ell≤
      firstSaving c (d+x) w q wo B
        (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell := by
  rw [common_saving_identity]
  have hm0 := le_max_right (w/3-wo) (0:ℝ)
  have hm1 := le_max_left (w/3-wo) (0:ℝ)
  by_cases h : 0≤d-c-2*w+wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem main_saving_lower (c d x q B sigma delta reserve : ℝ)
    (hc : 0≤ c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q) :
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+x) 0 q 0 B
        (x+max (d-c) 0+2*sigma+delta+reserve) (sigma/3) := by
  have hh := common_saving_lower c d x 0 q 0 B sigma 2 delta reserve (sigma/3)
    hc (by norm_num) hq (by norm_num) hB hallow
  norm_num only [zero_div,sub_zero,add_zero,mul_zero,max_self] at hh
  linarith

theorem error_penalty_le (l sigma : ℝ) (hl : 0≤l) (hu : l≤ sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0≤2*sigma/3 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [Nat.cast_ofNat,ite_false,ite_true,
    one_mul,sub_zero] <;> apply max_le <;> linarith

theorem error_saving_lower (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤ c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤ sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_le l sigma hl hu k hk]

theorem main_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j=
      (K0-j)+max (d-c) 0+2*sigma+delta+reserve := by
  rw [mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem error_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z)
    (p : O) (k : ℕ) :
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j=
      (K0-j)+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        sigma+delta+reserve := by
  rw [errorCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

open CenteredMomentFirstScale

end SevenEighths.CenteredMomentCommonRadiusSaving

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedCommonRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstMixedAllowance CenteredMomentCommonRadiusSaving
local notation "O" => ActualEisensteinCubic.O

theorem column_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    0≤ c ∧ 0≤q ∧ 0≤extractedAllowance I J Z ∧
      3*c-5*d≤6*extractedAllowance I J Z+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have hm := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  refine ⟨hc,hq.1,?_,?_⟩
  · unfold extractedAllowance; positivity
  · unfold extractedAllowance; linarith [hq.2]

theorem actual_main_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  convert (preTransparency := .instances) main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert (preTransparency := .instances) error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

end SevenEighths.CenteredMomentFirstMixedCommonRadius

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedNormalization
open CenteredMomentDescentLedger CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O" => ActualEisensteinCubic.O

theorem exceptional_reference_identity (Z V C D NE NR K Q w wo B j g ell:ℝ)
    (hZ:1<Z)(hV:0<V)(hC:0<C)(hD:0<D)(hE:0<NE)(hR:0<NR)(hK:0<K)(hQ:0<Q):
    let c:=Real.logb Z C;
    let d:=Real.logb Z D;
    let q:=Real.logb Z Q;
    let K0:=Real.logb Z (NE*NR*V^2/(K*C*D));
    let M:=Real.logb Z K+q-Real.logb Z NE-Real.logb Z NR;
    (V/C)*Z^(-wo)*(V/C/Z^w)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      (Q*(V/C)^2*Z^B)=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo B g ell):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hzlog:Real.log Z≠0:=ne_of_gt (Real.log_pos hZ)
  dsimp only
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi];positivity
  · simp only [Set.mem_Ioi];positivity
  · simp (disch := positivity) only [Real.log_div,Real.log_mul,Real.log_rpow,Real.log_pow]
    unfold firstSaving Real.logb
    rw [Real.log_div,Real.log_mul,Real.log_mul,Real.log_pow,
      Real.log_mul,Real.log_mul] <;> try positivity
    field_simp
    ; ring

theorem actual_error_weight (p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(k:ℕ)
    (hk:k=1 ∨ k=6 ∨ k=7):
    localErrorCost p (k-1)≤Z^(-errorMoving p Z k):=by
  have hn:1≤normValue p:=normValue_ge_one p hp
  have hnpos:0<normValue p:=normValue_pos p hp
  have he:Z^(-(Real.logb Z (normValue p)))=(normValue p)⁻¹:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le,
      Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hnpos]
  rcases hk with rfl|rfl|rfl
  · simpa [localErrorCost,errorMoving,normValue] using he.ge
  · norm_num only [Nat.reduceSub,localErrorCost,errorMoving,ite_true,neg_zero,Real.rpow_zero]
    change (1-(normValue p)⁻¹)^2≤1
    have hi:0≤(normValue p)⁻¹:=inv_nonneg.mpr hnpos.le
    have hu:(normValue p)⁻¹≤1:=inv_le_one_of_one_le₀ hn
    nlinarith
  · simpa [localErrorCost,errorMoving,normValue] using he.ge

end SevenEighths.CenteredMomentFirstMixedNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentFirstScale IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

lemma commonPart_of_equal_support (C D:Ideal O)(hC:C≠0)
    (hCD:primeSupport C=primeSupport D):commonPart C D=C := by
  have he:commonPart C D=commonPart C C:=by
    simp only [commonPart,commonSupport,←hCD]
  exact he.trans (commonPart_self C hC)

lemma nominal_equal_support (C D E:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(K V:ℝ):
    firstNominalScale C D E K V=
      (E.absNorm:ℝ)*(Ideal.span {activeConductor C D}).absNorm*V^2/
        (K*(C.absNorm:ℝ)*D.absNorm) := by
  rw [firstNominalScale,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentFirstExceptionalPrefactor

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalizationActual
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedNormalizationActual
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedAllowance
open CenteredMomentDescentLedger CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentFirstScale ConcreteTraceCRT
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O"=>HeckeFamily.O

theorem actual_reference_width (η τ:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(K Z:ℝ)(_hK:0<K)(_hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    Real.logb Z K+Real.logb Z (τ.modulus.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost:=by
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hq:=norm_pos _ η.modulus_ne_bot
  have hfixed:=fixedPresentationCost_pos
  rw [fixed_presentation_norm η τ C D E hmod]
  simp only [eisEmbedding_norm_sq_eq_absNorm_span]
  simp (disch := positivity) only [Real.logb_mul]
  ring

theorem actual_exceptional_reference (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g w wo ell:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*Z^(-wo)*(V/(C.absNorm:ℝ)/Z^w)^((1:ℝ)/3)*
      (Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo (allowance C D Z) g ell):=by
  have hh:=exceptional_reference_identity Z V (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)
    ((Ideal.span {activeConductor C D}).absNorm:ℝ) K (τ.modulus.absNorm:ℝ)
    w wo (allowance C D Z) j g ell hZ hV (norm_pos C hC.1) (norm_pos D hD.1)
    (norm_pos _ (subsetGenerator_supported C D hC E).1) (active_norm_pos C D) hK
    (norm_pos _ τ.modulus_ne_bot)
  dsimp only at hh ⊢
  rw [actual_reference_width η τ C D hC E K Z hK hZ hmod] at hh
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  exact hh

theorem actual_error_reference_le (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*
      (V/(C.absNorm:ℝ)/(normValue p)^k)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) (errorRemoval p Z k) q
        (errorMoving p Z k) (allowance C D Z) g 0):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hCpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hnpos:=normValue_pos p hp
  have hh:=actual_exceptional_reference η τ C D hC hD hCD E K V Z j g
    (errorRemoval p Z k) (errorMoving p Z k) 0 hK hV hZ hmod
  dsimp only at hh ⊢
  rw [errorRemoval_power p hp Z hZ k,neg_zero,Real.rpow_zero,mul_one] at hh
  rw [←hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (actual_error_weight p hp Z hZ k hk) (by positivity)

end SevenEighths.CenteredMomentFirstMixedNormalizationActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalCap
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalCap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

local instance instDecidableEq_solutions_rd64199_1 {κ:Type*}:DecidableEq κ:=Classical.decEq _
lemma fixed_presentation_log_nonneg (Z:ℝ)(hZ:1<Z):0≤Real.logb Z fixedPresentationCost:=by
  have h₁:(1:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h₂:(1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
  apply Real.logb_nonneg hZ
  unfold fixedPresentationCost
  nlinarith

lemma extracted_allowance_eq (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(Z:ℝ):extractedAllowance C D Z=allowance C D Z:=by
  simp only [extractedAllowance,allowance,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

end SevenEighths.CenteredMomentFirstMixedExceptionalCap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedDiagonal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedDiagonal
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedExceptionalCap
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstExceptionalPrefactor CenteredMomentDescentLedger
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O

theorem actual_common_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z w wo branch sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hw:0≤w)(hwo:0≤wo)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=nominalLog C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    (V/(C.absNorm:ℝ))*Z^(-wo)*
      Z^(K0+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve)*
      (V/(C.absNorm:ℝ)/Z^w)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        branch*sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hnc:=norm_pos C hC.1
  have hnd:=norm_pos D hD.1
  have hne:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hnr:=active_norm_pos C D
  have hnq:=norm_pos _ τ.modulus_ne_bot
  have hη:=norm_pos _ η.modulus_ne_bot
  have hf:=fixedPresentationCost_pos
  have hc:0≤Real.logb Z (C.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
  have hd:0≤Real.logb Z (D.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have hallow:=allowance_nonneg C D Z
  have hfix:=fixed_presentation_log_nonneg Z hZ
  have hm:max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-2*w+wo) 0≤
      Real.logb Z (D.absNorm:ℝ)+wo:=max_le (by linarith) (by linarith)
  have he:eps*(Real.logb Z (C.absNorm:ℝ)+w)≥0:=mul_nonneg heps (add_nonneg hc hw)
  have hq:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  have hnom:nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z=
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+2*Real.logb Z V-
      Real.logb Z K-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ):=by
    rw [nominalLog,nominal_equal_support C D _ hC.1 hD.1 hCD K V]
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
    ring
  dsimp only
  apply (Real.logb_le_iff_le_rpow hZ (by positivity)).mp
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_rpow hz hZ.ne',Real.logb_rpow_eq_mul_logb_of_pos,Real.logb_pow]
  rw [hnom]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hq,hm,he,hfix,hallow]

theorem actual_main_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (V/(C.absNorm:ℝ))*mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve*(V/(C.absNorm:ℝ))^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve+eps*Real.logb Z V):=by
  simpa only [mainCommonRadius,zero_mul,mul_zero,sub_zero,add_zero,neg_zero,
    Real.rpow_zero,mul_one,div_one] using
    actual_common_diagonal η τ C D hC hD hCD E K V Z 0 0 2 sigma delta reserve eps
      hK hV hZ (le_refl _) (le_refl _) heps hmod

theorem actual_error_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k*(V/(C.absNorm:ℝ)/(normValue p)^k)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hcpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hl:0≤Real.logb Z (normValue p):=Real.logb_nonneg hZ (normValue_ge_one p hp)
  have hw:0≤errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:0≤errorMoving p Z k:=by unfold errorMoving;split_ifs <;> positivity
  have hh:=actual_common_diagonal η τ C D hC hD hCD E K V Z
    (errorRemoval p Z k) (errorMoving p Z k) 1 sigma delta reserve eps hK hV hZ hw hwo heps hmod
  dsimp only at hh
  rw [one_mul,errorRemoval_power p hp Z hZ k] at hh
  apply le_trans ?_ hh
  unfold errorCommonRadius
  gcongr
  exact actual_error_weight p hp Z hZ k hk

end SevenEighths.CenteredMomentFirstMixedDiagonal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalLow
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalLow
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

local instance instDecidableEq_solutions_rd64199_2 {κ:Type*}:DecidableEq κ:=Classical.decEq _
theorem actual_main_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0< mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hl : 0 ≤ Real.logb Z (normValue p0) :=
    Real.logb_nonneg hZ (normValue_ge_one p0 hp.1.ne_zero)
  have hw : 0 ≤ errorRemoval p0 Z k := by unfold errorRemoval; positivity
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0<errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

end SevenEighths.CenteredMomentFirstMixedExceptionalLow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedExceptionalLow CenteredMomentFirstMixedDiagonal
open CenteredMomentSuccessorPaidParameters
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

lemma actual_valuation_mass : (∑i:Fin 3,16*(errorIndex i+2:ℝ)^2)=1872 := by
  norm_num [Fin.sum_univ_succ,errorIndex]

theorem actual_error_average (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (f:elementPool P→Fin 3→Ray→ℝ)(E:ℝ)(_hE:0≤E)
    (hf:∀p i χ,f p i χ≤E):
    (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
        1872*(Fintype.card Ray:ℝ)*E := by
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hc:Fintype.card (elementPool P)=P.card:=by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  have hh:(∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
      ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,E:=by
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>hf p i χ)) (by positivity)
  apply (mul_le_mul_of_nonneg_left hh (by positivity:0≤1/(P.card:ℝ))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Finset.sum_mul,actual_valuation_mass,hc]
  field_simp

lemma main_paid_core (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    Z^(-ell)*mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0≤
      Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have he:mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0=
      Z^(ell+deficit/6+paid-allowance):=by
    dsimp [mainCores,reference]
    rw [Real.rpow_sub hz]
    field_simp
  rw [he,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

lemma error_paid_core (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)
    (q V C Z allowance Kerror deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0≤Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have hpv:=normValue_pos p hp
  have hw:=actual_error_weight p hp Z hZ k hk
  have hs:localErrorCost p (k-1)*Z^(errorMoving p Z k)≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hz.le (errorMoving p Z k))
    rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have he:errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0=
      (localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^(deficit/6+paid-allowance):=by
    dsimp [errorCores,reference]
    rw [Real.rpow_sub hz,show errorRemoval p Z k+deficit/6+paid=
      errorRemoval p Z k+(deficit/6+paid) by ring,Real.rpow_add hz,errorRemoval_power p hp Z hZ k]
    field_simp
  rw [he]
  calc
    _≤1*Z^(deficit/6+paid-allowance):=mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _≤Z^(deficit+paid):=by rw [one_mul];apply Real.rpow_le_rpow_of_exponent_le hZ.le;linarith

theorem actual_main_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤ sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hr:0< mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  have havg:Z^(-sigma/3)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=main_paid_core (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod hK hV
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          4*sigma/3+5*(delta+reserve)/6):=by
      convert (preTransparency := .instances) hh using 1 ; dsimp [mainCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod
    have hc0:0≤ mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 2:=by
      dsimp [mainCores,reference];positivity
    apply (mul_le_mul_of_nonneg_right havg hc0).trans
    rw [one_mul]
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving):=by
      convert (preTransparency := .instances) ht using 1 ; dsimp [mainCores,reference] ; ring
    have ht':=mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hz.le (-sigma/3))
    apply ht'.trans
    calc
      _≤1*(Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving)):=mul_le_mul_of_nonneg_right havg (by positivity)
      _≤_:=by
        rw [one_mul,←Real.rpow_add hz]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        dsimp [lossVector]
        linarith

theorem actual_error_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤ sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (p:O)(hp:p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k;
    ∀j:Fin 4,errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hpdata:=elementPool_data _ (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0:p≠0:=hpdata.1.ne_zero
  have hr:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by unfold errorCommonRadius;positivity
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=error_paid_core p hp0 k hk (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod M H Sbad hbad p hp k hk hK hV
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          3*sigma/2+5*(delta+reserve)/6):=by
      convert (preTransparency := .instances) hh using 1 ; dsimp [errorCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod p hp0 k hk
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert (preTransparency := .instances) ht using 1 ; dsimp [errorCores,reference] ; ring
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

lemma shortened_power (V q:ℝ)(k:ℕ)(alpha:ℝ)(hV:0≤V)(hq:0≤q):
    (V/q^k)^alpha=V^alpha*(q^k)^(-alpha):=by
  rw [Real.div_rpow hV (pow_nonneg hq k),Real.rpow_neg (pow_nonneg hq k),div_eq_mul_inv]

theorem averaged_coefficients_bound (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (Z ell primeLoss mainFactor:ℝ)(hZ:1<Z)(hloss:0≤primeLoss)
    (hfactor:0≤ mainFactor)(hcard:Z^(ell-primeLoss)≤(P.card:ℝ))
    (H main loss:Fin 4→ℝ)(error:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hH:∀j,0≤H j)(hm:∀j,Z^(-ell)*main j≤Z^(loss j))
    (he:∀p i χ j,error p i χ j≤Z^(loss j)):
    ∀j,averagedCoefficients P mainFactor H main error j≤
      56*(mainFactor+1872*(Fintype.card Ray:ℝ))*H j*Z^(loss j+primeLoss) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hinv:(1/(P.card:ℝ))≤Z^(-ell+primeLoss):=by
    have hh:=one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz _) hcard
    simpa [one_div,←Real.rpow_neg hz.le,neg_sub,sub_eq_add_neg,add_comm] using hh
  intro j
  have hm':main j≤Z^(ell+loss j):=by
    have hh:=mul_le_mul_of_nonneg_left (hm j) (Real.rpow_nonneg hz.le ell)
    rw [←mul_assoc,←Real.rpow_add hz,add_neg_cancel,Real.rpow_zero,one_mul,
      ←Real.rpow_add hz] at hh
    exact hh
  have hmain:(1/(P.card:ℝ))*main j≤Z^(loss j+primeLoss):=by
    calc
      _≤(1/(P.card:ℝ))*Z^(ell+loss j):=mul_le_mul_of_nonneg_left hm' (by positivity)
      _≤Z^(-ell+primeLoss)*Z^(ell+loss j):=mul_le_mul_of_nonneg_right hinv (by positivity)
      _=Z^(loss j+primeLoss):=by rw [←Real.rpow_add hz];congr 1;ring
  have herr:=actual_error_average P hne hp hbad (fun p i χ=>H j*error p i χ j)
    (H j*Z^(loss j)) (mul_nonneg (hH j) (Real.rpow_nonneg hz.le _)) (fun p i χ=>mul_le_mul_of_nonneg_left (he p i χ j) (hH j))
  have hl:Z^(loss j)≤Z^(loss j+primeLoss):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have herr':(1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)≤
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss)):=
    herr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (hH j)) (by positivity))
  calc
    _=56*(mainFactor*H j*((1/(P.card:ℝ))*main j)+
      (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
        16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)):=by
      unfold averagedCoefficients;ring
    _≤56*(mainFactor*H j*Z^(loss j+primeLoss)+
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss))):=by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hmain (mul_nonneg hfactor (hH j))) herr') (by norm_num)
    _=_:=by ring

theorem actual_low_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving rmain;
    let error:=fun (p:elementPool P) (i:Fin 3) (χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (rerror p i χ);
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    rmain Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      (rerror p i χ) Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

theorem source_normalized_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(alpha:Fin 4→ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
        (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C ^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor (fun _=>1)
        (fun j=>(V/C)*amain j*(V/C)^(alpha j)/reference q V C Z allowance)
        (fun p i χ j=>(V/C)*localErrorCost p (errorIndex i)*aerror p i χ j*
          (V/C/(normValue p)^(errorIndex i+1))^(alpha j)/reference q V C Z allowance) j := by
  have hx:0<V/C:=div_pos hV hC
  have hnorm:∀p:O,0≤normValue p:=by intro p;unfold normValue;positivity
  intro j
  have hden:reference q V C Z allowance≠0:=by unfold reference;positivity
  have he:CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C ^eps*(b^N)^(alpha j)*((V/C)*sourceCoefficients P mainFactor amain aerror alpha j*
        (V/C)^(alpha j)/reference q V C Z allowance):=by
    unfold CenteredMomentFirstCommonReferencePower.normalizedPower reference
    rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_neg hZ.le]
    field_simp
  rw [he]
  congr 1
  unfold sourceCoefficients averagedCoefficients
  simp only [one_mul]
  simp only [shortened_power (V/C) _ _ _ hx.le (hnorm _)]
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul]
  ring_nf

lemma main_core_power (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):
    ∀j,mainCores q V C Z allowance Kmain ell deficit paid eps saving r j=
      (V/C)*mainPowers q Z Kmain ell deficit paid saving r j*
        (V/C)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [mainCores,mainPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

lemma error_core_power (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):
    ∀j,errorCores p k q V C Z allowance Kerror deficit paid eps saving r j=
      (V/C)*localErrorCost p (k-1)*errorPowers p k q Z Kerror deficit paid saving r j*
        (V/C/(normValue p)^k)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [errorCores,errorPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

theorem actual_power_reference_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(H:Fin 4→ℝ)(Kmain ell deficit paid saving rmain:ℝ)
    (Kerror rerror:elementPool P→Fin 3→Ray→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P) (i:Fin 3) (χ:Ray) (j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C ^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor H
        (mainCores q V C Z allowance Kmain ell deficit paid eps saving rmain)
        (fun p i χ=>errorCores p (errorIndex i+1) q V C Z allowance (Kerror p i χ)
          deficit paid eps saving (rerror p i χ)) j := by
  dsimp only
  intro j
  rw [source_normalized_identity P mainFactor b V C q Z allowance eps N _ _ _ hV hC hq hZ j]
  congr 1
  unfold averagedCoefficients
  simp only [one_mul]
  rw [main_core_power]
  congr 2
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    rw [error_core_power]
    simp only [Nat.add_sub_cancel]
    ring

end SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstHighGaussianUniformPowers
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

lemma finite_power_budget (upper nc Z eps Bcommon deficit primeLoss G F seed:ℝ)
    (N:ℕ)(hupper:1≤upper)(hnc:0≤nc)(hZ:1<Z)(heps:0≤eps)(heps1:eps≤1)
    (hncap:nc≤Z^Bcommon)(hG:0≤G)(_hF:0≤F)(_hseed:0<seed)
    (H srcLoss actualLoss:Fin 4→ℝ)(hH:∀j,0≤H j)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    nc^eps*(∑j:Fin 4,(upper^N)^(powers eps j)*
      (G*H j*Z^(deficit+actualLoss j+primeLoss)))≤
      (upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+actualLoss j):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hncPow:nc^eps≤Z^(eps*Bcommon):=by
    have hh:=Real.rpow_le_rpow hnc hncap heps
    simpa only [←Real.rpow_mul hz.le,mul_comm Bcommon eps] using hh
  have hu:1≤upper^N:=one_le_pow₀ hupper
  have hup (j:Fin 4):(upper^N)^(powers eps j)≤upper^N:=by
    have hp:powers eps j≤1:=by fin_cases j <;> simp [powers] <;> linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu hp
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj0:=hH j
  have hu0:0≤upper:=zero_le_one.trans hupper
  calc
    _≤Z^(eps*Bcommon)*(upper^N*(G*(F*Z^(srcLoss j)/seed)*Z^(deficit+actualLoss j+primeLoss))):=by
      apply mul_le_mul hncPow _ (by positivity) (by positivity)
      apply mul_le_mul (hup j) _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left (hbound j) hG
    _=(upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*Z^(srcLoss j+actualLoss j):=by
      calc
        _=(upper^N*G*F/seed)*(Z^(eps*Bcommon)*Z^(srcLoss j)*Z^(deficit+actualLoss j+primeLoss)):=by ring
        _=_:=by
          rw [←Real.rpow_add hz, ←Real.rpow_add hz]
          rw [show eps*Bcommon + srcLoss j + (deficit+actualLoss j+primeLoss) =
            (deficit+eps*Bcommon+primeLoss)+(srcLoss j+actualLoss j) by ring,
            Real.rpow_add hz]
          ring

end SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstNormalizedGaussianPowers
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstNormalizedGaussianPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

theorem actual_normalized_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:0≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (C.absNorm:ℝ)^eps*∑j:Fin 4,(upper^N)^(alpha j)*
        (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
          Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss)) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hz:=zero_lt_one.trans hZ
  have hn:=actual_power_reference_identity
    (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))) ((Mamp+2*sigma)/(sigma/6))
    upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z (allowance C D Z) eps N H
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid saving rmain
    (fun p i χ=>errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1))
    rerror hV hc hq hz
  have hav:=actual_low_four_coefficients M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod H hH rmain rerror
  dsimp only at hn hav
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [hn j]
  have hpos:0≤(C.absNorm:ℝ)^eps*(upper^N)^(CenteredMomentSecondChildPowerBudget.powers eps j):=by positivity
  exact (mul_le_mul_of_nonneg_left (hav j) hpos).trans_eq (by ring)

end SevenEighths.CenteredMomentEnergyFirstNormalizedGaussianPowers

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FirstLowHomogeneousPowers
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

open CenteredMomentEnergyFirstHighGaussianUniformPowers

theorem actual_low_homogeneous_four_powers_oai
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed)
    (rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  have ha:=CenteredMomentEnergyFirstNormalizedGaussianPowers.actual_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod
    upper N (zero_le_one.trans hupper) H hH rmain rerror
  dsimp only at ha ⊢
  apply ha.trans
  exact finite_power_budget upper (C.absNorm:ℝ) Z eps Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss
    (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))) F seed N
    hupper (Nat.cast_nonneg _) hZ heps heps1 hncap (by positivity) hF hseed H
    srcLoss (lossVector sigma delta reserve paid eps Mcap saving) hH hbound

end SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers.actual_low_homogeneous_four_powers_oai := @OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers.actual_low_homogeneous_four_powers_oai
