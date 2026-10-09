-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSecondNonexceptionalAggregate.source_part_harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:53:08.515865+00:00
-- url     : https://prove2.me/submissions/baa97286-4103-4000-9967-265c5558011c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Rankin
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentRankin
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem prime_norm_ge_two (P : Ideal O) (hp : Prime P) : 2 ≤ Ideal.absNorm P := by
  have h0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro hn
    exact hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hn))
  omega

theorem primeMass_nonneg (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ primeMass P δ := by
  apply inv_nonneg.mpr
  have hn : (1:ℝ) < Ideal.absNorm P := by exact_mod_cast (prime_norm_ge_two P hp)
  exact (sub_pos.mpr (Real.one_lt_rpow hn hδ)).le

theorem primeMass_le_fixed (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    primeMass P δ ≤ ((2:ℝ)^δ-1)⁻¹ := by
  apply inv_anti₀ (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hδ))
  exact sub_le_sub_right (Real.rpow_le_rpow (by norm_num)
    (by exact_mod_cast prime_norm_ge_two P hp) hδ.le) 1

theorem uniform_primeMass_product (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Ideal O), (∀ P ∈ S,Prime P) →
      (∏ P ∈ S,primeMass P δ) ≤ C := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2:ℝ)))
  let small : Finset (Ideal O) := (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  let B : ℝ := max 1 (((2:ℝ)^δ-1)⁻¹)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B^small.card,pow_pos (zero_lt_one.trans_le hB) _,?_⟩
  intro S hp
  have hs (P : Ideal O) (hP : P ∈ S∩small) : primeMass P δ ≤ B :=
    (primeMass_le_fixed P (hp P (Finset.mem_inter.mp hP).1) δ hδ).trans (le_max_right _ _)
  have hl (P : Ideal O) (hP : P ∈ S\small) : primeMass P δ ≤ 1 := by
    have hn : N < Ideal.absNorm P := by
      by_contra hn
      apply (Finset.mem_sdiff.mp hP).2
      simpa only [small,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using le_of_not_gt hn
    have hpow := hN (Ideal.absNorm P) hn.le
    apply inv_le_one_of_one_le₀
    linarith
  have he : S=(S∩small)∪(S\small) := by
    ext P
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hdis : Disjoint (S∩small) (S\small) := Finset.disjoint_left.mpr
    (fun P hP hQ => (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)
  rw [he,Finset.prod_union hdis]
  have hleft : (∏ P ∈ S∩small,primeMass P δ) ≤ B^small.card := by
    calc
      _ ≤ ∏ _P ∈ S∩small,B := Finset.prod_le_prod
        (fun P hP => primeMass_nonneg P (hp P (Finset.mem_inter.mp hP).1) δ hδ) hs
      _ = B^(S∩small).card := by simp
      _ ≤ _ := pow_le_pow_right₀ hB (Finset.card_le_card Finset.inter_subset_right)
  have hright : (∏ P ∈ S\small,primeMass P δ) ≤ 1 :=
    Finset.prod_le_one (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ) hl
  exact (mul_le_mul hleft hright (Finset.prod_nonneg
    (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ)) (by positivity)).trans_eq (mul_one _)

theorem local_power_sum (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) (K : ℕ) :
    (∑ n ∈ Finset.range K,((Ideal.absNorm P:ℝ)^(n+1))^(-δ)) ≤ primeMass P δ := by
  let q : ℝ := (Ideal.absNorm P:ℝ)^δ
  have hNP : (1:ℝ)<Ideal.absNorm P := by exact_mod_cast prime_norm_ge_two P hp
  have hq : 1 < q := Real.one_lt_rpow hNP hδ
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hsum := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).summable.sum_le_tsum
    (Finset.range K) (fun n _ => mul_nonneg hr0 (pow_nonneg hr0 n))
  rw [((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).tsum_eq] at hsum
  have he (n : ℕ) : ((Ideal.absNorm P:ℝ)^(n+1))^(-δ)=q⁻¹*(q⁻¹)^n := by
    rw [← Real.rpow_natCast_mul (by linarith : (0:ℝ)≤Ideal.absNorm P),mul_comm,
      Real.rpow_mul_natCast (by linarith : (0:ℝ)≤Ideal.absNorm P),Real.rpow_neg (by linarith),pow_succ]
    dsimp only [q]
    ring
  simp_rw [he]
  apply hsum.trans_eq
  change q⁻¹*(1-q⁻¹)⁻¹=(q-1)⁻¹
  field_simp

end SevenEighths.CenteredMomentRankin

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RankinCount
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinCount
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentRankin
local notation "O" => ActualEisensteinCubic.O

theorem powerCode_reconstruct (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) :
    I=∏ P : R,(P:Ideal O)^(powerCode R I P+1) := by
  have he (P : R) : powerCode R I P+1=(normalizedFactors I).count (P:Ideal O) := by
    have hp : (P:Ideal O) ∈ primeSupport I := hR ▸ P.property
    have hc := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    dsimp only [powerCode]
    omega
  simp_rw [he]
  calc
    I=(normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
    _=∏ P ∈ (normalizedFactors I).toFinset,P^(normalizedFactors I).count P := Finset.prod_multiset_count _
    _=∏ P : R,(P:Ideal O)^(normalizedFactors I).count (P:Ideal O) := by
      rw [Finset.prod_coe_sort R (fun P : Ideal O => P^(normalizedFactors I).count P)]
      change _=∏ P ∈ R,P^(normalizedFactors I).count P
      rw [← hR]
      rfl

theorem powerCode_injOn (R : Finset (Ideal O)) (S : Finset (Ideal O))
    (hS : ∀ I ∈ S,I ≠ 0) (hR : ∀ I ∈ S,primeSupport I=R) :
    Set.InjOn (powerCode R) S := by
  intro I hI J hJ he
  rw [powerCode_reconstruct R I (hS I hI) (hR I hI),powerCode_reconstruct R J (hS J hJ) (hR J hJ),he]

theorem ideal_mass_eq (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) (δ : ℝ) :
    (Ideal.absNorm I:ℝ)^(-δ)=
      ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(powerCode R I P+1))^(-δ) := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)^(-δ))
    (powerCode_reconstruct R I hI hR)
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] at he
  rw [he]
  exact (Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) _).symm

theorem fixed_support_mass (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      (∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ)) ≤ C := by
  obtain ⟨C,hC,hprod⟩ := uniform_primeMass_product δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hsupport
  let K : ℕ := S.sup (fun I => Finset.univ.sup (powerCode R I))+1
  let mass : (R → ℕ) → ℝ := fun v => ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(v P+1))^(-δ)
  have hm (v : R → ℕ) : 0 ≤ mass v := Finset.prod_nonneg
    (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  have hsub : S.image (powerCode R) ⊆ Fintype.piFinset (fun _P : R => Finset.range K) := by
    intro v hv
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro P
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := powerCode R I) (Finset.mem_univ P)).trans
      (Finset.le_sup (f := fun I => Finset.univ.sup (powerCode R I)) hI))
  calc
    _ = ∑ v ∈ S.image (powerCode R),mass v := by
      rw [Finset.sum_image (powerCode_injOn R S hS hsupport)]
      apply Finset.sum_congr rfl
      intro I hI
      exact ideal_mass_eq R I (hS I hI) (hsupport I hI) δ
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _P : R => Finset.range K),mass v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hm v)
    _ = ∏ P : R,∑ n ∈ Finset.range K,((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ) := by
      exact (Finset.prod_univ_sum (fun _P : R => Finset.range K)
        (fun P n => ((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ))).symm
    _ ≤ ∏ P : R,primeMass P δ := Finset.prod_le_prod
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
      (fun P _ => local_power_sum P (hR P P.property) δ hδ K)
    _ ≤ C := by
      have he := Finset.prod_coe_sort R (fun P => primeMass P δ)
      rw [he]
      exact hprod R hR

theorem fixed_support_count (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^δ := by
  obtain ⟨C,hC,hmass⟩ := fixed_support_mass δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hs X hX hN
  have hterm (I : Ideal O) (hI : I ∈ S) : (1:ℝ) ≤ X^δ*(Ideal.absNorm I:ℝ)^(-δ) := by
    have hn : (0:ℝ)<Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
    have hr := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn.le (hN I hI) hδ.le)
      (Real.rpow_nonneg hn.le (-δ))
    simpa only [← Real.rpow_add hn,add_neg_cancel,Real.rpow_zero] using hr
  calc
    _ = ∑ _I ∈ S,(1:ℝ) := by simp
    _ ≤ ∑ I ∈ S,X^δ*(Ideal.absNorm I:ℝ)^(-δ) := Finset.sum_le_sum (fun I hI => hterm I hI)
    _ = X^δ*∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ) := (Finset.mul_sum _ _ _).symm
    _ ≤ X^δ*C := mul_le_mul_of_nonneg_left (hmass R S hR hS hs) (Real.rpow_nonneg hX.le _)
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentRankinCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondDiagonal
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem divisible_ideal_card (S : Finset (Ideal O)) (s : Ideal O) (hs : s ≠ 0)
    (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hY : 0 ≤ Y) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  by_cases hempty : S.Nonempty
  · have hquot (I : Ideal O) (hI : I ∈ S) : idealQuotient s I ≠ 0 :=
      ne_zero_of_dvd_ne_zero (hS I hI) (idealQuotient_dvd (hdiv I hI))
    have hbound (I : Ideal O) (hI : I ∈ S) := idealQuotient_norm_le hs (hdiv I hI) Y (hN I hI)
    obtain ⟨I,hI⟩ := hempty
    have hscale : 1 ≤ Y/(Ideal.absNorm s : ℝ) := by
      have hn : (1:ℝ) ≤ Ideal.absNorm (idealQuotient s I) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hquot I hI))
      exact hn.trans (hbound I hI)
    have hc := DescentFiberCost.finite_ideal_count_real (S.image (idealQuotient s)) _ hscale
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hquot I hI)
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hbound I hI)
    rw [Finset.card_image_of_injOn (fun I hI J hJ he => idealQuotient_injective_on s
      (hdiv I hI) (hdiv J hJ) he)] at hc
    convert (preTransparency := .instances) hc using 1 ; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.cast_zero]
    positivity

end SevenEighths.CenteredMomentSecondDiagonal

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

theorem commonRadical_ne_zero (I J : Ideal O) : commonRadical I J ≠ 0 :=
  support_product_ne_zero Finset.inter_subset_left

theorem commonRadical_squarefree (I J : Ideal O) : Squarefree (commonRadical I J) :=
  squarefree_support_product Finset.inter_subset_left

theorem commonRadical_support (I J : Ideal O) :
    primeSupport (commonRadical I J)=primeSupport I∩primeSupport J := by
  unfold primeSupport commonRadical
  rw [factors_support_product Finset.inter_subset_left]
  simp [primeSupport]

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

theorem old_mask_radical_count {α : Type*} (S : Finset α) (I J : α → Ideal O)
    (s : Ideal O) (hs : Squarefree s) (hs0 : s ≠ 0)
    (hI : ∀ a ∈ S,I a ≠ 0) (hJ : ∀ a ∈ S,J a ≠ 0)
    (hsi : ∀ a ∈ S,s ∣ I a) (hsj : ∀ a ∈ S,s ∣ J a)
    (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ a ∈ S,(Ideal.absNorm (commonRadical (I a) (J a)):ℝ) ≤ Y) :
    ((S.image (fun a => commonRadical (I a) (J a))).card:ℝ) ≤
      128*Y/(Ideal.absNorm s:ℝ) := by
  refine CenteredMomentSecondDiagonal.divisible_ideal_card _ s hs0 ?_ ?_ Y hY ?_
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact commonRadical_ne_zero _ _
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact old_mask_dvd_commonRadical s _ _ hs (hI a ha) (hJ a ha) (hsi a ha) (hsj a ha)
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact hN a ha

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSecondZeroEnergy
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

lemma heightCoeff_norm_le_one (η : Character) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoeff η t I‖≤1 := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm I:ℂ)^(Complex.I*t)‖=1 := by
    rw [show (Ideal.absNorm I:ℂ)=((Ideal.absNorm I:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp
  rw [heightCoeff,norm_mul,hp,mul_one]
  exact idealCoeff_norm_le_one η I

end SevenEighths.CenteredMomentSourceSecondZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSmooth
open CenteredMomentFirstWholeKernel CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem secondEffectiveScale_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : 0<secondEffectiveScale C D A K := by
  apply div_pos (mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hA))))
  exact mul_pos (CenteredMomentFirstScale.norm_pos C hC) (CenteredMomentFirstScale.norm_pos D hD)

end SevenEighths.CenteredMomentSecondWholeKernel

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RankinSubset
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinSubset
open IdealMobiusDivisorSum CenteredMomentRankinCount
local notation "O" => ActualEisensteinCubic.O

theorem supported_power_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O),
      (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I ⊆ primeSupport Q) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := fixed_support_count a ha
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Q hQ S hS hs X hX hN
  have hf : ∀ I ∈ S,primeSupport I ∈ (primeSupport Q).powerset :=
    fun I hI => Finset.mem_powerset.mpr (hs I hI)
  have he := Finset.card_eq_sum_card_fiberwise hf
  have hfiber (R : Finset (Ideal O)) (hR : R ∈ (primeSupport Q).powerset) :
      ((S.filter (fun I => primeSupport I=R)).card:ℝ) ≤ C*X^a := by
    apply hcount R _ (fun P hP => support_prime ((Finset.mem_powerset.mp hR) hP))
      (fun I hI => hS I (Finset.mem_filter.mp hI).1)
      (fun I hI => (Finset.mem_filter.mp hI).2) X hX
      (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  calc
    _ = ∑ R ∈ (primeSupport Q).powerset,((S.filter (fun I => primeSupport I=R)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _R ∈ (primeSupport Q).powerset,C*X^a := Finset.sum_le_sum hfiber
    _ = (2:ℝ)^(primeSupport Q).card*(C*X^a) := by simp
    _ ≤ (D*(Ideal.absNorm Q:ℝ)^ε)*(C*X^a) :=
      mul_le_mul_of_nonneg_right (hsub Q hQ) (mul_nonneg hC.le (Real.rpow_nonneg hX.le _))
    _ = _ := by ring

theorem supported_power_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1 ⊆ primeSupport Q ∧ primeSupport v.2 ⊆ primeSupport Q) →
      ∀ X Y : ℝ,0 < X → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X ∧ (Ideal.absNorm v.2:ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X^a*Y^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := supported_power_count a (ε/2) ha (by positivity)
  refine ⟨C ^2,pow_pos hC _,?_⟩
  intro Q hQ S hS hs X Y hX hY hN
  have hfst : ((S.image Prod.fst).card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ X hX ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).1
  have hsnd : ((S.image Prod.snd).card:ℝ) ≤ C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ Y hY ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).2
  have hin : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,Finset.mem_image_of_mem _ hv⟩
  have hn : (0:ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  calc
    _ ≤ ((S.image Prod.fst).card:ℝ)*((S.image Prod.snd).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hin).trans_eq (Finset.card_product _ _)
    _ ≤ (C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2))*(C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2)) :=
      mul_le_mul hfst hsnd (Nat.cast_nonneg _) (by positivity)
    _ = C ^2*X^a*Y^a*((Ideal.absNorm Q:ℝ)^(ε/2)*(Ideal.absNorm Q:ℝ)^(ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

end SevenEighths.CenteredMomentRankinSubset

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RankinLabels
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinLabels
open IdealMobiusDivisorSum CenteredMomentRankinRadical CenteredMomentRankinSubset
local notation "O" => ActualEisensteinCubic.O

theorem common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1=primeSupport v.2) →
      (∀ v ∈ S,s ∣ v.1 ∧ s ∣ v.2) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := supported_power_pair_count a ε ha hε
  refine ⟨128*C,by positivity,?_⟩
  intro s hs hs0 S hS heq hdiv X₁ X₂ Y hX₁ hX₂ hY hN hR
  let rad : Ideal O × Ideal O → Ideal O := fun v => commonRadical v.1 v.2
  have hfiber (R : Ideal O) (hRmem : R ∈ S.image rad) :
      ((S.filter (fun v => rad v=R)).card:ℝ) ≤ C*X₁^a*X₂^a*Y^ε := by
    obtain ⟨v,hv,hvR⟩ := Finset.mem_image.mp hRmem
    have hR0 : R ≠ 0 := hvR ▸ commonRadical_ne_zero v.1 v.2
    have hRN : (Ideal.absNorm R:ℝ) ≤ Y := hvR ▸ hR v hv
    have hb := hcount R hR0 (S.filter (fun v => rad v=R))
      (fun v hv => hS v (Finset.mem_filter.mp hv).1)
      (by
        intro w hw
        obtain ⟨hw,hwr⟩ := Finset.mem_filter.mp hw
        have he : primeSupport R=primeSupport w.1 := by
          rw [← hwr,commonRadical_support,← heq w hw,Finset.inter_self]
        rw [he,heq w hw]
        exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩)
      X₁ X₂ hX₁ hX₂ (fun w hw => hN w (Finset.mem_filter.mp hw).1)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hRN hε.le) (by positivity))
  have hrad := old_mask_radical_count S Prod.fst Prod.snd s hs hs0
    (fun v hv => (hS v hv).1) (fun v hv => (hS v hv).2)
    (fun v hv => (hdiv v hv).1) (fun v hv => (hdiv v hv).2) Y hY.le hR
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem rad hv)
  calc
    _ = ∑ R ∈ S.image rad,((S.filter (fun v => rad v=R)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _R ∈ S.image rad,C*X₁^a*X₂^a*Y^ε := Finset.sum_le_sum hfiber
    _ = ((S.image rad).card:ℝ)*(C*X₁^a*X₂^a*Y^ε) := by simp
    _ ≤ (128*Y/(Ideal.absNorm s:ℝ))*(C*X₁^a*X₂^a*Y^ε) :=
      mul_le_mul_of_nonneg_right hrad (by positivity)
    _ = _ := by rw [Real.rpow_add hY,Real.rpow_one]; ring

theorem partitioned_common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset ((Ideal O × Ideal O) × Finset (Ideal O)),
      (∀ v ∈ S,v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1.1=primeSupport v.1.2) →
      (∀ v ∈ S,s ∣ v.1.1 ∧ s ∣ v.1.2) →
      (∀ v ∈ S,v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.1.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := common_pair_count a (ε/2) ha (by positivity)
  obtain ⟨D,hD,hpow⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro s hs hs0 S hS heq hdiv hpart X₁ X₂ Y hX₁ hX₂ hY hN hR
  have hpairs := hcount s hs hs0 (S.image Prod.fst)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hS w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact heq w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hdiv w hw)
    X₁ X₂ Y hX₁ hX₂ hY
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hN w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hR w hw)
  have hfiber (v : Ideal O × Ideal O) (hv : v ∈ S.image Prod.fst) :
      ((S.filter (fun w => w.1=v)).card:ℝ) ≤ D*Y^(ε/2) := by
    have hin : (S.filter (fun w => w.1=v)).image Prod.snd ⊆
        (primeSupport (commonRadical v.1 v.2)).powerset := by
      intro A hA
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hw,hwe⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_powerset.mpr (hwe ▸ hpart w hw)
    have hinj : Set.InjOn (fun w : (Ideal O × Ideal O) × Finset (Ideal O) => w.2)
        (↑(S.filter (fun w => w.1=v)) : Set ((Ideal O × Ideal O) × Finset (Ideal O))) := by
      intro w hw z hz he
      exact Prod.ext ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm) he
    have hc : ((S.filter (fun w => w.1=v)).card:ℝ) ≤
        (2:ℝ)^(primeSupport (commonRadical v.1 v.2)).card := by
      have hb := Finset.card_le_card hin
      rw [Finset.card_image_of_injOn hinj,Finset.card_powerset] at hb
      exact_mod_cast hb
    obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp hv
    have hb := hpow (commonRadical v.1 v.2) (commonRadical_ne_zero _ _)
    have hn : (Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y := hwe ▸ hR w hw
    exact hc.trans (hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by positivity)) hD.le))
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem Prod.fst hv)
  calc
    _ = ∑ v ∈ S.image Prod.fst,((S.filter (fun w => w.1=v)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _v ∈ S.image Prod.fst,D*Y^(ε/2) := Finset.sum_le_sum hfiber
    _ = ((S.image Prod.fst).card:ℝ)*(D*Y^(ε/2)) := by simp
    _ ≤ (C*X₁^a*X₂^a*Y^(1+ε/2)/(Ideal.absNorm s:ℝ))*(D*Y^(ε/2)) :=
      mul_le_mul_of_nonneg_right hpairs (by positivity)
    _ = (C*D)*X₁^a*X₂^a*(Y^(1+ε/2)*Y^(ε/2))/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add hY]; congr 3; ring

end SevenEighths.CenteredMomentRankinLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DyadicCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma logb_four_mul (b : ℝ) (hb : 0<b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

theorem indices_card_log_bound (C R Z a b : ℝ) (hC : 1≤C) (hR : 0≤R)
    (hZ : 1≤Z) (ha : 0<a) (hab : a≤b) (hratio : b/a≤C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

theorem four_indices_subpower (C R ε : ℝ) (hC : 1≤C) (hR : 0≤R) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0<a j) → (∀j,a j≤b j) →
      (∀j,b j/a j≤C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0<K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hz : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentWholeDivisorShell
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma normKey_eq_iff (D : Ideal O) (hD : D≠0) (n : ℤ) :
    normKey D=n ↔ dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hn : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hl := Real.logb_le_logb (by norm_num : (1:ℝ)<2) (dyadicScale_pos n) hn
  have hu := Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<2) hn (dyadicScale_pos (n+1))
  simp only [logb_dyadicScale,Int.cast_add,Int.cast_one] at hl hu
  rw [normKey,Int.floor_eq_iff,←hl,←dyadicScale_add,←hu]

end SevenEighths.CenteredMomentWholeDivisorShell

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentDivisorAllocation CenteredMomentWholeDivisorShell
open CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma commonRadical_norm_le (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    (Ideal.absNorm (commonRadical I J):ℝ) ≤ min (I.absNorm:ℝ) J.absNorm := by
  have hd : commonRadical I J ∣ I ∧ commonRadical I J ∣ J := by
    constructor <;> apply (squarefree_dvd_iff _ _ (commonRadical_squarefree I J)).mpr
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).1)
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).2)
  apply le_min
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm hd.1)
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
      (map_dvd Ideal.absNorm hd.2)

lemma min_le_sqrt_mul (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    min x y ≤ Real.sqrt (x*y) := by
  apply (Real.le_sqrt (le_min hx hy) (mul_nonneg hx hy)).mpr
  rcases le_total x y with h|h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

lemma shell_scalar (e Y x y : ℝ) (he : 0<e) (hx : 0<x) (hy : 0<y)
    (hY : min x y ≤ Y) :
    (2*min x y)^(1+e)/Real.sqrt (x*y) ≤ 2^(1+e)*Y^e := by
  have hm : 0< min x y := lt_min hx hy
  have hsqrt : 0<Real.sqrt (x*y) := Real.sqrt_pos.2 (mul_pos hx hy)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hm.le,
    Real.rpow_add hm,Real.rpow_one]
  have hp := Real.rpow_le_rpow hm.le hY he.le
  have hs := min_le_sqrt_mul x y hx.le hy.le
  apply (div_le_iff₀ hsqrt).mpr
  calc
    _ ≤ 2^(1+e)*(Real.sqrt (x*y)*Y^e) := by gcongr
    _ = _ := by ring

theorem shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀(s : Ideal O),Squarefree s → s≠0 →
      ∀(S : Finset Label),(∀v∈S,Valid s v) → ∀Y T₁ T₂ : ℝ,
      0<T₁ → 0<T₂ → min T₁ T₂≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T₁≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*T₁ ∧
        T₂≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*T₂) →
      (∑v∈S,weight v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T₁ T₂ hT₁ hT₂ hTY hN hshell
  have hY : 0<Y := (lt_min hT₁ hT₂).trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hsq : 0<Real.sqrt (T₁*T₂) := Real.sqrt_pos.2 (mul_pos hT₁ hT₂)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*min T₁ T₂) hY hY (by positivity) hN (by
      intro v hv
      apply (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      exact min_le_min (hshell v hv).2.1.le (hshell v hv).2.2.2.le)
  calc
    _ ≤ ∑_v∈S,1/Real.sqrt (T₁*T₂) := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le hsq
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hshell v hv).1 (hshell v hv).2.2.1 hT₂.le (hT₁.le.trans (hshell v hv).1)
    _ = (S.card:ℝ)/Real.sqrt (T₁*T₂) := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*min T₁ T₂)^(1+e)/(s.absNorm:ℝ))/Real.sqrt (T₁*T₂) :=
      div_le_div_of_nonneg_right hc hsq.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*min T₁ T₂)^(1+e)/Real.sqrt (T₁*T₂)) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T₁ T₂ he hT₁ hT₂ hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

lemma norm_scale_bounds (I : Ideal O) (hI : I≠0) (Y : ℝ) (hY : (I.absNorm:ℝ)≤Y) :
    1≤dyadicScale (normKey I) ∧ dyadicScale (normKey I)≤Y := by
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hk : 0≤normKey I := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hn)
  refine ⟨?_,((normKey_eq_iff I hI _).mp rfl).1.trans hY⟩
  simpa only [dyadicScale,zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hk

lemma shell_norm_bounds (S : Finset Label) (n : ℤ×ℤ) (v : Label)
    (hv : v∈shell S n) (hC : v.1.1≠0) (hD : v.1.2≠0) :
    dyadicScale n.1≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*dyadicScale n.1 ∧
    dyadicScale n.2≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*dyadicScale n.2 := by
  have he := (Finset.mem_filter.mp hv).2
  have h₁ := (normKey_eq_iff v.1.1 hC n.1).mp (congrArg Prod.fst he)
  have h₂ := (normKey_eq_iff v.1.2 hD n.2).mp (congrArg Prod.snd he)
  exact ⟨h₁.1,h₁.2,h₂⟩

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)^2*(1+Real.log Z)^2 := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ (indices 1 (Z^B))×ˢ(indices 1 (Z^B)) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (h0 v hv).1 (Z^B) (hN v hv).1
    have hd := norm_scale_bounds v.1.2 (h0 v hv).2 (Z^B) (hN v hv).2
    apply Finset.mem_product.mpr
    constructor
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hc.1,hc.2.trans (by linarith)⟩
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hd.1,hd.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ)^2 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product] at hh
    exact_mod_cast (by simpa only [pow_two] using hh)
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  calc
    _ ≤ ((indices 1 (Z^B)).card:ℝ)^2 := hc
    _ ≤ ((3+B/Real.log 2)*(1+Real.log Z))^2 := by gcongr
    _ = _ := by ring

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,weight v)≤C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨C*K^2,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ×ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (hS v hv).1 (Z^B) (hN v hv).1
    have hm : min (dyadicScale n.1) (dyadicScale n.2)≤Z^B := by
      have heq : normKey v.1.1=n.1 := congrArg Prod.fst hkey
      exact (min_le_left _ _).trans (heq ▸ hc.2)
    exact hbound s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n.1) (dyadicScale n.2) (dyadicScale_pos _) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw (hS w (Finset.mem_filter.mp hw).1).1
        (hS w (Finset.mem_filter.mp hw).1).2.1)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K^2*(1+Real.log Z)^2)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K^2)*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

lemma log_square_subpower (d : ℝ) (hd : 0<d) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → (1+Real.log Z)^2≤C*Z^d := by
  let a : ℝ := d/2
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨(1+1/a)^2,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^a := Real.one_le_rpow hZ ha.le
  have hl := Real.log_le_rpow_div hz.le ha
  have hh : 1+Real.log Z≤(1+1/a)*Z^a := by
    calc
      _ ≤ Z^a+Z^a/a := add_le_add hp hl
      _ = _ := by ring
  calc
    _ ≤ ((1+1/a)*Z^a)^2 := by
      apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hh
    _ = (1+1/a)^2*Z^d := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le]
      congr 2
      dsimp [a]; ring

theorem common_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0<e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := by linarith
  have hZ1 : 1≤Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr; exact hlog Z hZ1
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end SevenEighths.CenteredMomentCommonHarmonicMass

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

theorem mem_partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (p : (Ideal O×Ideal O)×Finset (Ideal O)) :
    p∈partitionLabels S β Y ↔ p.1∈commonShell S β Y ∧
      p.2⊆IdealMobiusDivisorSum.primeSupport (commonRadical p.1.1 p.1.2) := by
  simp only [partitionLabels,Finset.mem_biUnion,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨q,hq,U,hU,rfl⟩
    exact ⟨hq,hU⟩
  · rintro ⟨hp,hU⟩
    exact ⟨p.1,hp,p.2,hU,rfl⟩

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C) :
    commonFrequencyGenerator C D≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (supported_element_ne_zero _ (commonPrime_supported C D hC P))

end SevenEighths.CenteredMomentSecondCanonicalFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem nonunitFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

end SevenEighths.CenteredMomentSecondCanonicalNonunit

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondActiveDyadic
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondActiveDyadic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicPartition CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondRetainedRows
local notation "O" => ActualEisensteinCubic.O

theorem sourceLower_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : ∀i,0<sourceLower C D A K i := by
  intro i
  fin_cases i
  · exact secondEffectiveScale_pos C D hC hD A hA K hK
  all_goals norm_num [sourceLower]

end SevenEighths.CenteredMomentSecondActiveDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentHeckeColumnWindow
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

lemma common_height_norm_le_one (η : Character) (t : ℝ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) :
    ‖heightCoeff η t C*star (heightCoeff η t D)‖≤1 := by
  rw [norm_mul,norm_star]
  have hc := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t C hC
  have hd := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t D hD
  nlinarith [norm_nonneg (heightCoeff η t C),norm_nonneg (heightCoeff η t D)]

end SevenEighths.CenteredMomentSecondBlockAggregate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondBlockCount
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondBlockCount
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondWholeKernel
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondBlockAggregate CenteredMomentSecondActiveCount
open CenteredMomentSecondRetainedRows
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondSectorColumns CenteredMomentSecondRetainedAggregate
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentDyadicCount
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentActiveSource
local notation "O" => ActualEisensteinCubic.O

lemma ideal_norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma sourceLower_le_upper (C D : Ideal O) (A : O) (K R H : ℝ) :
    ∀i,sourceLower C D A K i≤ sourceUpper C D A K R H i := by
  intro i
  fin_cases i
  · exact le_rfl
  all_goals exact le_max_left _ _

lemma source_ratio_bound (B L Cr Z : ℝ) (hB : 0≤B) (hL : 0≤L)
    (_hCr : 0<Cr) (hZ : 1≤Z)
    (C D : Ideal O) (hC : C≠0) (hD : D≠0) (A : O) (hA : A≠0)
    (K R H : ℝ) (hK : 0<K) (hR : R≤Cr*Z^L) (hH : H≤Z^B) :
    ∀i,sourceUpper C D A K R H i/sourceLower C D A K i≤
      max 1 (4*Cr)*Z^(B+L) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hc : 1≤ max 1 (4*Cr) := le_max_left _ _
  have hq : 1≤ max 1 (4*Cr)*Z^(B+L) := one_le_mul_of_one_le_of_one_le hc hp
  have hN := normValue_ge_one A hA
  have hNC := ideal_norm_ge_one C hC
  have hND := ideal_norm_ge_one D hD
  have hBpow : Z^B≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hLpow : Z^L≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hH' : H≤ max 1 (4*Cr)*Z^(B+L) :=
    hH.trans (hBpow.trans (le_mul_of_one_le_left (zero_le_one.trans hp) hc))
  have hR' : 4*R≤ max 1 (4*Cr)*Z^(B+L) := by
    calc
      _≤4*Cr*Z^L := by linarith
      _≤ max 1 (4*Cr)*Z^(B+L) :=
        mul_le_mul (le_max_right _ _) hLpow (Real.rpow_nonneg hz.le _) (by positivity)
  have hn (x d : ℝ) (hd : 1≤d) (hx : x≤ max 1 (4*Cr)*Z^(B+L)) :
      max 1 (x/d)≤ max 1 (4*Cr)*Z^(B+L) := by
    apply max_le hq
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).mpr
    exact hx.trans (le_mul_of_one_le_right (by positivity) hd)
  intro i
  fin_cases i
  · simpa [sourceUpper,sourceLower,
      div_self (secondEffectiveScale_pos C D hC hD A hA K hK).ne'] using hq
  · simpa [sourceUpper,sourceLower] using hn (4*R) (normValue A) hN hR'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm C) hNC hH'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm D) hND hH'

theorem sourceBlocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃D₀:ℝ,0<D₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),Supported C → Supported D →
      ∀(U:Finset (CommonIndex C D))(K R H:ℝ),0<K →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (SourceBlocks C D U K R H):ℝ)≤D₀*Z^ε := by
  obtain ⟨D₀,hD₀,hcount⟩ := four_indices_subpower (max 1 (4*Cr)) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨D₀,hD₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hc hZ
  intro C D hC hD U K R H hK hR hH
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  exact hc _ _ (sourceLower_pos C D hC.1 hD.1 _ hA K hK)
    (sourceLower_le_upper C D _ K R H)
    (source_ratio_bound B L Cr Z hB hL hCr hZ C D hC.1 hD.1 _ hA K R H hK hR hH)

lemma commonSubset_support (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    U.image Subtype.val⊆IdealMobiusDivisorSum.primeSupport (commonRadical C D) := by
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
  rw [commonRadical_support]
  exact Q.property

end SevenEighths.CenteredMomentSecondBlockCount

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
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
local notation "O" => ActualEisensteinCubic.O

lemma pairWeight_nonneg (C D : Ideal O) : 0≤pairWeight C D := by
  unfold pairWeight
  positivity

lemma activeSubsetLabel_injective (S : Finset (Ideal O)) (β : Ideal O→ℂ) :
    Function.Injective (activeSubsetLabel S β) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=>x.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective
    (congrArg (fun x=>x.2) he)
  cases hU
  rfl

lemma active_common_shell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (p : ActiveLabel S β) :
    p.val∈commonShell S β Y := by
  have hs := commonLabels_supported (activeSource S β) _ _ p.property
  have hn := commonLabel_norm_bounds S β Y hN _ _ p.property
  exact Finset.mem_filter.mpr ⟨p.property,
    (commonRadical_norm_le _ _ hs.1.1 hs.2.1).trans ((min_le_left _ _).trans hn.1)⟩

lemma activeSubsetLabel_mem (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (q : ActiveSubsets S β) :
    activeSubsetLabel S β q∈partitionLabels S β Y := by
  exact (mem_partitionLabels S β Y _).mpr
    ⟨active_common_shell S β Y hN q.1,commonSubset_support _ _ q.2⟩

lemma active_mass_le_partition (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) :
    (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
      pairWeight p.val.1 p.val.2)≤
    ∑v∈partitionLabels S β Y,pairWeight v.1.1 v.1.2 := by
  have he : (∑q : ActiveSubsets S β,pairWeight q.1.val.1 q.1.val.2)=
      ∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2 := Fintype.sum_sigma _
  rw [←he]
  let f := activeSubsetLabel S β
  calc
    _ = ∑v∈Finset.univ.image f,pairWeight v.1.1 v.1.2 := by
      rw [Finset.sum_image]
      · rfl
      · exact (activeSubsetLabel_injective S β).injOn
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv;obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hv
          exact activeSubsetLabel_mem S β Y hN q)
      (fun v _ _=>pairWeight_nonneg _ _)

lemma active_blocks_sum_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :
    (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)=
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ)*pairWeight p.val.1 p.val.2 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Fintype.sum_sigma _

theorem actual_active_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2)≤C*Z^δ/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn
  apply (active_mass_le_partition S β (Z^B) hn).trans
  apply hb Z hZ seed hs hs0 (partitionLabels S β (Z^B))
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β (Z^B) v).mp hv
    have hh:=active_common_data S β seed hs hm (Z^B) v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hn _ _
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^B) v).mp hv).1).1

theorem actual_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C₁,hC₁,hmass⟩:=actual_active_harmonic_mass B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩:=sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (2:ℝ)] with Z hb hZ
  intro seed hs hs0 S β hm hn K R H hK hR hH
  have hsum:=hmass Z hZ seed hs hs0 S β hm hn
  rw [active_blocks_sum_eq]
  calc
    _ ≤ ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (C₂*Z^(ε/2))*pairWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
      exact mul_le_mul_of_nonneg_right
        (hb _ _ hsupp.1 hsupp.2 U K R H hK hR hH) (pairWeight_nonneg _ _)
    _ = (C₂*Z^(ε/2))*(∑p : ActiveLabel S β,
        ∑U : Finset (CommonIndex p.val.1 p.val.2),pairWeight p.val.1 p.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (C₂*Z^(ε/2))*(C₁*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (C₂*C₁)*Z^ε/(seed.absNorm:ℝ) := by
      calc
        _ = (C₂*C₁)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z),add_halves]

end SevenEighths.CenteredMomentSecondBlockHarmonicMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondEnergySplit
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRestrictedEnergy
open CenteredMomentChildRows RayFourExpansion
local notation "O"=>HeckeFamily.O

theorem partEnergy_norm_le (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖≤
  ∑p∈liveLabels η S β,
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))‖
 :=by
  unfold partEnergy
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end SevenEighths.CenteredMomentSecondEnergySplit

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r55ddc9_1 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
lemma live_harmonic_sum_le (η:Character)(S:Finset (Ideal O))(β:Ideal O→ℂ)(K R H:ℝ):
    (∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,pairWeight p.val.1 p.val.2)≤
    ∑q:ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2:=by
  rw [CenteredMomentSecondBlockHarmonicMass.active_blocks_sum_eq]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _=>Finset.sum_nonneg (fun U _=>mul_nonneg (Nat.cast_nonneg _) (pairWeight_nonneg _ _)))

theorem part_energy_harmonic_bound (exceptional:Bool)(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(hV:0<V)(hE:0≤E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        pairWeight q.1.1.val.1 q.1.1.val.2):=by
  apply (div_le_div_of_nonneg_right
    (partEnergy_norm_le exceptional η χ Q m t S β W K Tsec Z ξ H) hV.le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          E*pairWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hb p hp U n
    _=E*(∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          pairWeight p.val.1 p.val.2):=by simp only [Finset.mul_sum]
    _≤_:=mul_le_mul_of_nonneg_left (live_harmonic_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

theorem source_part_harmonic_bound_oai (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z^L → H≤Z^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm exceptional η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (part_energy_harmonic_bound exceptional η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)

end SevenEighths.CenteredMomentSecondNonexceptionalAggregate

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentSecondNonexceptionalAggregate.source_part_harmonic_bound_oai := @OAI.SevenEighths.CenteredMomentSecondNonexceptionalAggregate.source_part_harmonic_bound_oai
