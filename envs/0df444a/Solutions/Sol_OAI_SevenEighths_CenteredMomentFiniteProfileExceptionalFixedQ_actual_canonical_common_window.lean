-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ.actual_canonical_common_window
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:55:50.696511+00:00
-- url     : https://prove2.me/submissions/eee11f44-5256-4d43-86da-a3e923f5aa48

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptionalCommon_actual_common_better_side

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier
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

namespace ActualEisensteinCubic

theorem quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa only [map_ofNat, Nat.cast_ofNat] using hz)

end ActualEisensteinCubic

end

end OAI
end

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.UniformPolynomialHeight
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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CompletedUnitRows
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open UnrestrictedIdealReindex (unitIdealEquiv span_unit_generator)

attribute [local instance] OAI.CompletedUnitRows.instFintypeUnitsO
lemma rowUnit_spec (z : ActualEisensteinCubic.O) (hz : z≠0) :
    (rowUnit z).val * idealGenerator (Ideal.span {z}) = z := by
  let p := unitIdealEquiv.symm ⟨z,hz⟩
  have hp : p.1.val*idealGenerator p.2.val=z :=
    congrArg Subtype.val (unitIdealEquiv.apply_symm_apply ⟨z,hz⟩)
  have hI : p.2.val=Ideal.span {z} := by
    rw [←hp,span_unit_generator]
  simpa only [rowUnit,dif_neg hz,←hI] using hp

lemma unitIdealPoint_inj (z w : ActualEisensteinCubic.O) (hz : z≠0) (hw : w≠0)
    (h : unitIdealPoint z=unitIdealPoint w) : z=w := by
  have hu : rowUnit z=rowUnit w := congrArg Prod.fst h
  have hI : Ideal.span {z}=Ideal.span {w} := congrArg Prod.snd h
  rw [←rowUnit_spec z hz,←rowUnit_spec w hw,hu,hI]

theorem sum_nonzero_element_le_units (T : Finset ActualEisensteinCubic.O) (hT : ∀z∈T,z≠0)
    (v : ActualEisensteinCubic.O→ℝ) (hv : ∀z,0≤v z) :
    (∑z∈T,v z) ≤ ∑u : ActualEisensteinCubic.Oˣ,∑I∈T.image (fun z=>Ideal.span {z}),
      v (u.val*idealGenerator I) := by
  let f : ActualEisensteinCubic.Oˣ×Ideal ActualEisensteinCubic.O→ℝ := fun p=>v (p.1.val*idealGenerator p.2)
  have hinj : Set.InjOn unitIdealPoint T := by
    intro z hz w hw he
    exact unitIdealPoint_inj z w (hT z hz) (hT w hw) he
  have he : (∑z∈T,v z)=∑p∈T.image unitIdealPoint,f p := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [f,unitIdealPoint]
    rw [rowUnit_spec z (hT z hz)]
  have hsub : T.image unitIdealPoint ⊆
      (Finset.univ : Finset ActualEisensteinCubic.Oˣ) ×ˢ T.image (fun z=>Ideal.span {z}) := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  rw [he]
  calc
    _ ≤ ∑p∈(Finset.univ : Finset ActualEisensteinCubic.Oˣ) ×ˢ T.image (fun z=>Ideal.span {z}),f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _=>hv _)
    _ = _ := by rw [Finset.sum_product]

lemma unit_card : Fintype.card ActualEisensteinCubic.Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

end CompletedUnitRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CenteredExceptionalCount
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredExceptionalCount
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem sixthQuotient_injective_on_remainder {I J : Ideal O}
    (hI : I ≠ 0) (hJ : J ≠ 0) (hr : sixthRemainder I = sixthRemainder J)
    (hq : sixthQuotient I = sixthQuotient J) : I = J := by
  rw [← sixth_normal_form I hI, ← sixth_normal_form J hJ, hr, hq]

theorem sixthRemainder_eq_of_profile {I R : Ideal O} (hR : R ≠ 0)
    (hprofile : ∀ P, valuation I P % 6 = valuation R P) : sixthRemainder I = R := by
  apply ideal_eq_of_valuation_eq (sixthRemainder_ne_zero I) hR
  intro P
  simpa only [sixthRemainder_valuation] using hprofile P

theorem forced_fourth_power_dvd (I D : Ideal O) (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    D ^ 4 ∣ sixthRemainder I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hD.ne_zero)
    (sixthRemainder_ne_zero I)).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  change valuation (D ^ 4) P ≤ valuation (sixthRemainder I) P
  rw [valuation_pow, sixthRemainder_valuation]
  have hcount : valuation D P ≤ 1 := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD) P
  by_cases hP : P ∈ normalizedFactors D
  · rw [hfour P hP]
    omega
  · have hz : valuation D P = 0 := Multiset.count_eq_zero.mpr hP
    simp only [hz, mul_zero, Nat.zero_le]

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ (Ideal.absNorm J : ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hIJ))

theorem forced_fourth_power_norm_le (I D : Ideal O) (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    (Ideal.absNorm D : ℝ) ^ 4 ≤ (Ideal.absNorm (sixthRemainder I) : ℝ) := by
  simpa only [map_pow, Nat.cast_pow] using
    norm_le_of_dvd (sixthRemainder_ne_zero I) (forced_fourth_power_dvd I D hD hfour)

theorem sixth_normal_form_norm (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm (sixthRemainder I) : ℝ) *
      (Ideal.absNorm (sixthQuotient I) : ℝ) ^ 6 = (Ideal.absNorm I : ℝ) := by
  have h := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ)) (sixth_normal_form I hI)
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using h

theorem sixthQuotient_norm_le (I : Ideal O) (hI : I ≠ 0) {H : ℝ} (hH : 0 ≤ H)
    (hNI : (Ideal.absNorm I : ℝ) ≤ H) :
    (Ideal.absNorm (sixthQuotient I) : ℝ) ≤
      (H / Ideal.absNorm (sixthRemainder I)) ^ (1 / 6 : ℝ) := by
  have hr := norm_pos (sixthRemainder_ne_zero I)
  have hp : (Ideal.absNorm (sixthQuotient I) : ℝ) ^ (6 : ℝ) ≤
      H / Ideal.absNorm (sixthRemainder I) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, le_div_iff₀ hr]
    rw [mul_comm, sixth_normal_form_norm I hI]
    exact hNI
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (div_nonneg hH hr.le)
      (by norm_num : (0 : ℝ) < 6)).mpr hp

theorem ideal_count_fixed_remainder (S : Finset (Ideal O)) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  by_cases hne : S.Nonempty
  · have hqbound (I : Ideal O) (hI : I ∈ S) :
        (Ideal.absNorm (sixthQuotient I) : ℝ) ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
      simpa only [hrem I hI] using sixthQuotient_norm_le I (hS I hI) hH (hN I hI)
    obtain ⟨I, hI⟩ := hne
    have hscale : 1 ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      (norm_one_le (sixthQuotient_ne_zero I)).trans (hqbound I hI)
    have hinj : Set.InjOn sixthQuotient S := by
      intro I hI J hJ he
      exact sixthQuotient_injective_on_remainder (hS I hI) (hS J hJ)
        ((hrem I hI).trans (hrem J hJ).symm) he
    have hc := DescentFiberCost.finite_ideal_count_real (S.image sixthQuotient)
      ((H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) hscale
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact sixthQuotient_ne_zero I)
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact hqbound I hI)
    rwa [Finset.card_image_iff.mpr hinj] at hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg hH (norm_pos hR).le) _)

theorem element_count_le_six_ideal_count (S : Finset O) (hS : ∀ z ∈ S, z ≠ 0) :
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) := by
  have h := CompletedUnitRows.sum_nonzero_element_le_units S hS (fun _ => 1)
    (fun _ => by norm_num)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    CompletedUnitRows.unit_card, Nat.cast_ofNat] using h

theorem element_count_fixed_remainder (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ z ∈ S, z ≠ 0)
    (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  have hc := ideal_count_fixed_remainder (S.image (fun z => Ideal.span {z})) R hR H hH
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact Ideal.span_singleton_eq_bot.not.mpr (hS z hz))
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hrem z hz)
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hN z hz)
  calc
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) :=
      element_count_le_six_ideal_count S hS
    _ ≤ 6 * (128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) := by gcongr
    _ = 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by ring

theorem element_count_power_scale (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : Z ^ d ≤ (Ideal.absNorm R : ℝ)) (hS : ∀ z ∈ S, z ≠ 0)
    (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hM : 0 ≤ C * Z ^ m := mul_nonneg hC (Real.rpow_nonneg hZ.le _)
  have hdiv : (C * Z ^ m) / Ideal.absNorm R ≤ (C * Z ^ m) / Z ^ d :=
    div_le_div_of_nonneg_left hM (Real.rpow_pos_of_pos hZ _) hRnorm
  calc
    (S.card : ℝ) ≤ 768 * ((C * Z ^ m) / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      element_count_fixed_remainder S R hR _ hM hS hrem hN
    _ ≤ 768 * ((C * Z ^ m) / Z ^ d) ^ (1 / 6 : ℝ) := by gcongr
    _ = 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      rw [mul_div_assoc, ← Real.rpow_sub hZ, Real.mul_rpow hC (Real.rpow_nonneg hZ.le _),
        ← Real.rpow_mul hZ.le]
      rw [show (m - d) * (1 / 6 : ℝ) = (m - d) / 6 by ring, mul_assoc]

theorem sixthRemainder_eq_of_prime_profile {I R : Ideal O} (hR : R ≠ 0)
    (hprofile : ∀ P, Prime P → valuation I P % 6 = valuation R P) :
    sixthRemainder I = R := by
  apply sixthRemainder_eq_of_profile hR
  intro P
  by_cases hP : Prime P
  · exact hprofile P hP
  · have hI0 : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    have hR0 : valuation R P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    simp only [hI0, hR0, Nat.zero_mod]

theorem element_count_power_scale_family (S : Finset O) (Rs : Finset (Ideal O))
    (hRs : ∀ R ∈ Rs, R ≠ 0) (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : ∀ R ∈ Rs, Z ^ d ≤ (Ideal.absNorm R : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) ∈ Rs)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * (Rs.card : ℝ) * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hcard : (S.card : ℝ) =
      ∑ R ∈ Rs, ((S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (t := Rs) hrem
  rw [hcard]
  calc
    _ ≤ ∑ R ∈ Rs, 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      apply Finset.sum_le_sum
      intro R hR
      exact element_count_power_scale
        (S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)) R (hRs R hR)
        Z C m d hZ hC (hRnorm R hR)
        (fun z hz => hS z (Finset.mem_filter.mp hz).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => hN z (Finset.mem_filter.mp hz).1)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end SevenEighths.CenteredExceptionalCount
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem split_at_prime (I P : Ideal O) (hI : I ≠ 0) [P.IsMaximal] :
    ∃ J : Ideal O, I = P ^ valuation I P * J ∧ J ≠ 0 ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ valuation I Q
  have hsplit : I = P ^ valuation I P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
      _ = ∏ Q ∈ S, Q ^ valuation I Q := Finset.prod_multiset_count _
      _ = P ^ valuation I P * J := by
        by_cases hP : P ∈ S
        · exact (Finset.mul_prod_erase S (fun Q => Q ^ valuation I Q) hP).symm
        · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
            (fun h => hP (Multiset.mem_toFinset.mpr h))
          simp only [J, Finset.erase_eq_of_notMem hP, hz, pow_zero, one_mul]
  refine ⟨J, hsplit, ?_, ?_⟩
  · intro hz
    apply hI
    rw [hsplit, hz, mul_zero]
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hp := prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

theorem exists_unit_probe (Q K P : Ideal O) (hK : K ≠ 0) [P.IsMaximal]
    (hQP : IsCoprime Q P) (u : (O ⧸ P)ˣ) :
    ∃ n : O, n - 1 ∈ Q ∧ IsCoprime (Ideal.span {n}) K ∧
      Ideal.Quotient.mk P n = (u : O ⧸ P) := by
  obtain ⟨J, hsplit, hJ, hJP⟩ := split_at_prime K P hK
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) P (hQP.mul_left hJP)
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk P n) = (1, (u : O ⧸ P)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnJ : Ideal.Quotient.mk J n = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn)
  have hcJ : IsCoprime (Ideal.span {n}) J :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnJ ▸ isUnit_one)
  have hcP : IsCoprime (Ideal.span {n}) P :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnP ▸ u.isUnit)
  refine ⟨n, Ideal.mul_le_left hn, ?_, hnP⟩
  rw [hsplit]
  exact hcP.pow_right.mul_right hcJ

theorem valuation_mod_six_of_unit_agreement (Q K I J P : Ideal O)
    (hK : K ≠ 0) (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (heq : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      idealRowHom n I = idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  obtain ⟨I₀, hsplitI, hI₀, hcI⟩ := split_at_prime I P hI.1
  obtain ⟨J₀, hsplitJ, hJ₀, hcJ⟩ := split_at_prime J P hJ.1
  have hsI : CanonicalQuadraticSieve.Supported I₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitI ▸ hI)).2
  have hsJ : CanonicalQuadraticSieve.Supported J₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitJ ▸ hJ)).2
  have hpows : actualSextic P hg ^ valuation I P = actualSextic P hg ^ valuation J P := by
    apply MulChar.ext
    intro u
    obtain ⟨n, hn, hcK, hnP⟩ := exists_unit_probe (Q * I₀ * J₀) K P hK
      ((hQP.mul_left hcI).mul_left hcJ) u
    have hval := heq n (Ideal.mul_le_left (Ideal.mul_le_left hn)) hcK
    have hIn : n - 1 ∈ I₀ := Ideal.mul_le_right (Ideal.mul_le_left hn)
    have hJn : n - 1 ∈ J₀ := Ideal.mul_le_right hn
    rw [hsplitI, hsplitJ, map_mul, map_mul, map_pow, map_pow,
      idealRowHom_congr_mod I₀ n 1 hIn, idealRowHom_congr_mod J₀ n 1 hJn,
      idealRowHom_one_supported I₀ hsI, idealRowHom_one_supported J₀ hsJ,
      mul_one, mul_one, idealRowHom_prime n P hg, hnP] at hval
    simpa only [MulChar.pow_apply_coe] using hval
  have hm := (pow_eq_pow_iff_modEq.mp hpows)
  rw [actualSextic_order_six P hg hchar] at hm
  exact hm

theorem elementCoeff_eq_one_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hψ : Q ≤ ψ.modulus)
    (n : O) (hn : n - 1 ∈ Q) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = 1 := by
  have hn0 : n ≠ 0 := by
    intro hz
    have h1 : (1 : O) ∈ Q := by simpa [hz] using Q.neg_mem hn
    exact hQ ((Ideal.eq_top_iff_one Q).mpr h1)
  rw [elementCoeff_eq_of_inducedBy χ ψ h n hn0 hc]
  change ψ.residue (Ideal.Quotient.mk ψ.modulus n) = 1
  rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (hψ hn), map_one]

theorem local_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q K I J P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (hrow₁ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₁ n = elementCoeff η n * idealRowHom n I)
    (hrow₂ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₂ n = elementCoeff η n * idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  let L := ((K * η.modulus) * χ₁.modulus) * χ₂.modulus
  have hL : L ≠ 0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero hK η.modulus_ne_bot) χ₁.modulus_ne_bot) χ₂.modulus_ne_bot
  apply valuation_mod_six_of_unit_agreement Q L I J P hL hI hJ hg hchar hQP
  intro n hn hc
  obtain ⟨⟨⟨hcK, hcη⟩, hc₁⟩, hc₂⟩ :=
    (show ((IsCoprime (Ideal.span {n}) K ∧ IsCoprime (Ideal.span {n}) η.modulus) ∧
      IsCoprime (Ideal.span {n}) χ₁.modulus) ∧ IsCoprime (Ideal.span {n}) χ₂.modulus from by
        simpa only [L, IsCoprime.mul_right_iff] using hc)
  have he₁ := elementCoeff_eq_one_of_inducedBy χ₁ ψ₁ h₁ Q hQ hψ₁ n hn hc₁
  have he₂ := elementCoeff_eq_one_of_inducedBy χ₂ ψ₂ h₂ Q hQ hψ₂ n hn hc₂
  rw [hrow₁ n hn hcK] at he₁
  rw [hrow₂ n hn hcK] at he₂
  have hη : elementCoeff η n ≠ 0 := MulChar.apply_ne_zero_iff.mpr
    ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcη)
  exact mul_left_cancel₀ hη (he₁.trans he₂.symm)

theorem actual_row_on_fixed_units (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1)
    (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (n : O) (hn : n - 1 ∈ Ideal.span {(72 : O)})
    (hc : IsCoprime (Ideal.span {n}) (Ideal.span {m})) :
    elementCoeff χ n = elementCoeff η n * idealRowHom n (Ideal.span {r}) := by
  have hd72 : λ₀ ^ 2 ∣ (72 : O) := ActualEisensteinCubic.lambda_sq_dvd_three.trans
    (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩)
  have hp : λ₀ ^ 2 ∣ n - 1 := hd72.trans (Ideal.mem_span_singleton.mp hn)
  rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hp]
  change ((elementCoeff η n * coprimalityMask m n) * numeratorBadTwist u a b r hr n) *
    idealRowHom n (Ideal.span {r}) = _
  have hm : coprimalityMask m n = 1 := by
    change (if IsCoprime m n then (1 : ℂ) else 0) = 1
    simp only [((Ideal.isCoprime_span_singleton_iff _ _).mp hc).symm, ite_true]
  rw [hm, numeratorBadTwist_periodic u a b r hr n 1 hn, map_one, mul_one, mul_one]

theorem actual_rows_good_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u₁ u₂ : Oˣ) (a₁ b₁ a₂ b₂ : ℕ) (r₁ r₂ : O)
    (hr₁ : CanonicalQuadraticSieve.Supported (Ideal.span {r₁}))
    (hr₂ : CanonicalQuadraticSieve.Supported (Ideal.span {r₂}))
    (hpr₁ : λ₀ ^ 2 ∣ r₁ - 1) (hpr₂ : λ₀ ^ 2 ∣ r₂ - 1)
    (hx₁ : f ^ 4 * z₁ = (u₁ : O) * λ₀ ^ a₁ * (2 : O) ^ b₁ * r₁)
    (hx₂ : f ^ 4 * z₂ = (u₂ : O) * λ₀ ^ a₂ * (2 : O) ^ b₂ * r₂)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P)
    (hchar : ringChar (O ⧸ P) ≠ 2) (hQP : IsCoprime Q P) :
    valuation (Ideal.span {r₁}) P % 6 = valuation (Ideal.span {r₂}) P % 6 := by
  apply local_rows_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q (Ideal.span {m})
    (Ideal.span {r₁}) (Ideal.span {r₂}) P hQ (Ideal.span_singleton_eq_bot.not.mpr hm)
    hψ₁ hψ₂ hr₁ hr₂ hg hchar hQP
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₁ m f z₁ hmLam hm2 u₁ a₁ b₁ r₁ hr₁ hpr₁ hx₁ hχ₁ n (hQ72 hn) hc
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₂ m f z₂ hmLam hm2 u₂ a₂ b₂ r₂ hr₂ hpr₂ hx₂ hχ₂ n (hQ72 hn) hc

theorem valuation_span_eq_zero_of_not_mem (x : O) (P : Ideal O) (hx : x ∉ P) :
    valuation (Ideal.span {x}) P = 0 := by
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ P.zero_mem)
  apply Multiset.count_eq_zero.mpr
  intro hP
  have hle := ((Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr hx0)).mp hP).2
  exact hx (hle (Ideal.subset_span (by simp)))

theorem valuation_supported_numerator (x : O) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : r ≠ 0) (hx : x = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P : Ideal O) (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P) :
    valuation (Ideal.span {x}) P = valuation (Ideal.span {r}) P := by
  have hu : Ideal.span {(u : O)} = (1 : Ideal O) := by
    simpa only [Ideal.one_eq_top] using (Ideal.span_singleton_eq_top.mpr u.isUnit)
  have hl0 : Ideal.span {λ₀} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have h20 : Ideal.span {(2 : O)} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hr0 : Ideal.span {r} ≠ (0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hr
  rw [hx]
  simp only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu, one_mul]
  rw [valuation_mul _ _ _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ h20)) hr0,
    valuation_mul _ _ _ (pow_ne_zero _ hl0) (pow_ne_zero _ h20), valuation_pow, valuation_pow,
    valuation_span_eq_zero_of_not_mem λ₀ P hg, valuation_span_eq_zero_of_not_mem (2 : O) P h2]
  omega

theorem valuation_mod_six_cancel_frozen (A I J P : Ideal O)
    (hA : A ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : valuation (A * I) P % 6 = valuation (A * J) P % 6) :
    valuation I P % 6 = valuation J P % 6 := by
  rw [valuation_mul A I P hA hI, valuation_mul A J P hA hJ] at h
  exact Nat.ModEq.add_left_cancel' (valuation A P) h

theorem actual_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨u₁, a₁, b₁, r₁, hr₁, hpr₁, hx₁⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₁) (mul_ne_zero (pow_ne_zero _ hf) hz₁)
  obtain ⟨u₂, a₂, b₂, r₂, hr₂, hpr₂, hx₂⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₂) (mul_ne_zero (pow_ne_zero _ hf) hz₂)
  have hr₁0 := Ideal.span_singleton_eq_bot.not.mp hr₁.1
  have hr₂0 := Ideal.span_singleton_eq_bot.not.mp hr₂.1
  have h := actual_rows_good_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q hQ hQ72 hψ₁ hψ₂
    m f z₁ z₂ hm hmLam hm2 u₁ u₂ a₁ b₁ a₂ b₂ r₁ r₂ hr₁ hr₂ hpr₁ hpr₂ hx₁ hx₂
    hχ₁ hχ₂ P hg (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP
  rw [← valuation_supported_numerator _ u₁ a₁ b₁ r₁ hr₁0 hx₁ P hg h2,
    ← valuation_supported_numerator _ u₂ a₂ b₂ r₂ hr₂0 hx₂ P hg h2,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at h
  exact valuation_mod_six_cancel_frozen _ _ _ P
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ hf))
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) h

theorem local_row_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q K I P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ : Q ≤ ψ.modulus) (hI : CanonicalQuadraticSieve.Supported I)
    [P.IsMaximal] (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hrow : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ n = elementCoeff η n * idealRowHom n I) :
    valuation I P % 6 = 0 := by
  have hzero : valuation (1 : Ideal O) P % 6 = 0 := by
    simp only [valuation, normalizedFactors_one, Multiset.count_zero, Nat.zero_mod]
  rw [← hzero]
  apply valuation_mod_six_of_unit_agreement (Q * η.modulus) (K * χ.modulus) I 1 P
    (mul_ne_zero hK χ.modulus_ne_bot) hI
    (by constructor; exact one_ne_zero; simp only [normalizedFactors_one, Multiset.notMem_zero, false_implies, implies_true]) hg hchar
    (hQP.mul_left hηP)
  intro n hn hc
  obtain ⟨hcK, hcχ⟩ := IsCoprime.mul_right_iff.mp hc
  have hnQ := Ideal.mul_le_left hn
  have hη : elementCoeff η n = 1 := by
    change η.residue (Ideal.Quotient.mk η.modulus n) = 1
    rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn), map_one]
  have he := elementCoeff_eq_one_of_inducedBy χ ψ h Q hQ hψ n hnQ hcχ
  rw [hrow n hnQ hcK, hη, one_mul] at he
  simpa only [map_one] using he

theorem actual_row_numerator_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m f z : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P) :
    valuation (Ideal.span {f ^ 4 * z}) P % 6 = 0 := by
  obtain ⟨u, a, b, r, hr, hpr, hx⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z) (mul_ne_zero (pow_ne_zero _ hf) hz)
  rw [valuation_supported_numerator _ u a b r (Ideal.span_singleton_eq_bot.not.mp hr.1) hx P hg h2]
  apply local_row_valuation_zero η χ ψ h Q (Ideal.span {m}) (Ideal.span {r}) P hQ
    (Ideal.span_singleton_eq_bot.not.mpr hm) hψ hr hg
    (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP hηP
  intro n hn hc
  exact actual_row_on_fixed_units η χ m f z hmLam hm2 u a b r hr hpr hx hχ n (hQ72 hn) hc

theorem actual_row_forced_residue_four (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hA2 : valuation (Ideal.span {A}) P % 6 = 2) :
    valuation (Ideal.span {z}) P % 6 = 4 := by
  have he := actual_row_numerator_valuation_zero η χ ψ h Q hQ hQ72 hψ m 1 (A * z)
    hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2 hχ P hg h2 hQP hηP
  simp only [one_pow, one_mul] at he
  rw [← Ideal.span_singleton_mul_span_singleton, valuation_mul _ _ _
    (Ideal.span_singleton_eq_bot.not.mpr hA) (Ideal.span_singleton_eq_bot.not.mpr hz),
    Nat.add_mod, hA2] at he
  omega

theorem actual_forced_fourth_power (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2) :
    D ^ 4 ∣ sixthRemainder (Ideal.span {z}) ∧
      (Ideal.absNorm D : ℝ) ^ 4 ≤ Ideal.absNorm (sixthRemainder (Ideal.span {z})) := by
  have hf : ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4 := by
    intro P hP
    have hp := prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    obtain ⟨hg, h2, hQP, hηP, hA2⟩ := hgood P hP
    exact actual_row_forced_residue_four η χ ψ h Q hQ hQ72 hψ m A z hm hA hz hmLam hm2 hχ
      P hg h2 hQP hηP hA2
  exact ⟨forced_fourth_power_dvd _ D hD hf, forced_fourth_power_norm_le _ D hD hf⟩

theorem fixed_inducing_rows_profile (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨χ₁, ψ₁, _, hi₁, hψ₁, hχ₁⟩ := h₁
  obtain ⟨χ₂, ψ₂, _, hi₂, hψ₂, hχ₂⟩ := h₂
  have he := actual_rows_profile η χ₁ χ₂ ψ₁ ψ₂ hi₁ hi₂ Q hQ hQ72 hψ₁ hψ₂
    m 1 (A * z₁) (A * z₂) hm one_ne_zero (mul_ne_zero hA hz₁) (mul_ne_zero hA hz₂)
    hmLam hm2 hχ₁ hχ₂ P hg h2 hQP
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at he
  exact valuation_mod_six_cancel_frozen _ _ _ P (Ideal.span_singleton_eq_bot.not.mpr hA)
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) he

theorem fixed_inducing_rows_same_remainder (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (hsector : ∀ P ∈ S, valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6) :
    sixthRemainder (Ideal.span {z₁}) = sixthRemainder (Ideal.span {z₂}) := by
  apply sixthRemainder_eq_of_prime_profile (sixthRemainder_ne_zero _)
  intro P hP
  rw [sixthRemainder_valuation]
  by_cases hPS : P ∈ S
  · exact hsector P hPS
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨hg, h2, hQP⟩ := houtside P hP hPS
    exact fixed_inducing_rows_profile η Q hQ hQ72 m A z₁ z₂ hm hA hz₁ hz₂ hmLam hm2
      h₁ h₂ P hg h2 hQP

theorem fixed_inducing_remainder_card (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z) :
    (T.image (fun z => sixthRemainder (Ideal.span {z}))).card ≤ 6 ^ S.card := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  let code : Ideal O → (S → Fin 6) :=
    fun R P => ⟨valuation R P.val % 6, Nat.mod_lt _ (by decide)⟩
  have hinj : (Rs : Set (Ideal O)).InjOn code := by
    intro R hR R' hR' he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hR'
    apply fixed_inducing_rows_same_remainder η Q hQ hQ72 m A z z' hm hA (hT z hz) (hT z' hz')
      hmLam hm2 (hex z hz) (hex z' hz') S houtside
    intro P hP
    have hh := congrArg (fun f : S → Fin 6 => (f ⟨P, hP⟩).val) he
    simpa only [code, sixthRemainder_valuation, Nat.mod_mod] using hh
  have hc := Finset.card_le_card_of_injOn code (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Rs] using hc

theorem fixed_inducing_row_count (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ S.card * C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  have hRs : ∀ R ∈ Rs, R ≠ 0 := by
    intro R hR
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hR
    exact sixthRemainder_ne_zero _
  have hRnorm : ∀ R ∈ Rs, Z ^ (2 * F) ≤ (Ideal.absNorm R : ℝ) := by
    intro R hR
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨χ, ψ, _, hi, hψ, hχ⟩ := hex z hz
    have hf := (actual_forced_fourth_power η χ ψ hi Q hQ hQ72 hψ m A z hm hA
      (hT z hz) hmLam hm2 hχ D hD hgood).2
    calc
      Z ^ (2 * F) = (Z ^ (F / 2)) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        congr 1
        norm_num
        ring
      _ ≤ (Ideal.absNorm D : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) hDnorm _
      _ ≤ _ := hf
  have hcount := element_count_power_scale_family T Rs hRs Z C M (2 * F) hZ hC hRnorm hT
    (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩) hN
  have hcard : (Rs.card : ℝ) ≤ (6 : ℝ) ^ S.card := by
    exact_mod_cast fixed_inducing_remainder_card η Q hQ hQ72 m A hm hA hmLam hm2 S houtside T hT hex
  apply hcount.trans
  gcongr

theorem outside_fixed_support (Q : Ideal O) (hQ : Q ≠ 0)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (P : Ideal O) (hP : Prime P)
    (hPS : P ∉ (normalizedFactors Q).toFinset) :
    λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := (inferInstance : P.IsMaximal).eq_of_le hJ.ne_top hPJ
    apply hPS
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hQ).mpr
    exact ⟨Ideal.isPrime_of_prime hP, hPJ' ▸ hQJ⟩
  have h72 : (72 : O) ∉ P := by
    intro hh
    have hle : Q ≤ P := hQ72.trans ((Ideal.span_singleton_le_iff_mem _).mpr hh)
    have he := Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [sup_eq_right.mpr hle] at he
    exact hP.ne_one (by simpa only [Ideal.one_eq_top] using he)
  have hl : λ₀ ∣ (72 : O) :=
    (dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans
      (ActualEisensteinCubic.lambda_sq_dvd_three.trans (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩))
  have h2 : (2 : O) ∣ 72 := ⟨36, by norm_num⟩
  refine ⟨?_, ?_, hcop⟩
  · intro hh
    obtain ⟨v, hv⟩ := hl
    exact h72 (hv ▸ P.mul_mem_right v hh)
  · intro hh
    obtain ⟨v, hv⟩ := h2
    exact h72 (hv ▸ P.mul_mem_right v hh)

theorem fixed_support_exceptional_count (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) :=
  fixed_inducing_row_count η Q hQ hQ72 m A hm hA hmLam hm2
    (normalizedFactors Q).toFinset (outside_fixed_support Q hQ0 hQ72) T hT hex
    D hD hgood Z C M F hZ hC hDnorm hN

end SevenEighths.CenteredExceptionalProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ChildRows
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildRows
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily HeckeRowClosure
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem old_coefficient_nonzero_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) : IsCoprime (Ideal.span {e}) η.modulus :=
  (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp he)

theorem old_coefficient_prime_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) (P : Ideal O) (hP : P ∣ Ideal.span {e}) :
    IsCoprime η.modulus P :=
  (old_coefficient_nonzero_coprime η e he).symm.of_isCoprime_of_dvd_right hP

theorem childCharacter_coprime (η : Character) (χ : RayCharacter) (Q P : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (hQP : IsCoprime Q P)
    (hηP : IsCoprime η.modulus P) : IsCoprime (childCharacter η χ).modulus P := by
  have h12 : IsCoprime (Ideal.span {(12 : O)}) P :=
    hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr (hQ.trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6, by norm_num⟩)))
  rw [childCharacter_modulus]
  exact (hηP.mul_left h12).of_isCoprime_of_dvd_left
    (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)

theorem separated_exceptional_count (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A e : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (he : elementCoeff η e ≠ 0) (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors D,
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P ∧ P ∣ Ideal.span {e} ∧
        CenteredExceptionalCount.valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  apply CenteredExceptionalProfile.fixed_support_exceptional_count
    (childCharacter η χ) Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex D hD
      ?_ Z C M F hZ hC hDnorm hN
  intro P hP
  obtain ⟨hg,h2,hQP,hPe,hval⟩ := hgood P hP
  exact ⟨hg,h2,hQP,childCharacter_coprime η χ Q P hQ72 hQP
    (old_coefficient_prime_coprime η e he P hPe),hval⟩

end SevenEighths.CenteredMomentChildRows

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Forcing
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentForcing
open UniqueFactorizationMonoid CenteredExceptionalCount CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem valuation_product (S : Finset ι) (I : ι → Ideal O)
    (hI : ∀ i ∈ S, I i ≠ 0) (Q : Ideal O) :
    valuation (∏ i ∈ S, I i) Q = ∑ i ∈ S, valuation (I i) Q := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,valuation,normalizedFactors_one,Multiset.count_zero]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      valuation_mul _ _ _ (hI i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hI j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))]

theorem valuation_prime (P Q : Ideal O) (hP : Prime P) :
    valuation P Q = if P = Q then 1 else 0 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro R hR; simpa only [Multiset.mem_singleton.mp hR] using hP))
  simp only [valuation,hf,Multiset.count_singleton]
  simp only [eq_comm]

omit [Fintype ι] in
theorem valuation_prime_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    valuation (∏ j ∈ S, P j) (P i) = if i ∈ S then 1 else 0 := by
  rw [valuation_product S P (fun j _ => (hp j).ne_zero)]
  simp only [valuation_prime _ _ (hp _), hinj.eq_iff]
  simp

theorem valuation_prime_power_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (n : ι → ℕ) (i : ι) :
    valuation (∏ j, P j ^ n j) (P i) = n i := by
  rw [valuation_product Finset.univ _ (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  simp only [valuation_pow,valuation_prime _ _ (hp _),hinj.eq_iff,mul_ite,mul_one,mul_zero]
  simp

omit [DecidableEq ι] in
theorem movingIdeal_ne_zero (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : movingIdeal P c d V ≠ 0 := by
  unfold movingIdeal
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))

theorem movingIdeal_valuation (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι) :
    valuation (movingIdeal P c d V) (P i) = min (c i) (d i) + if i ∈ V then 1 else 0 := by
  rw [movingIdeal,valuation_mul _ _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)),
    valuation_prime_power_product P hp hinj, valuation_prime_product P hp hinj]

theorem forcing_valuation_two (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι)
    (i : ι) (hi : i ∈ forcingSet c d V) : valuation (movingIdeal P c d V) (P i) = 2 := by
  obtain ⟨hiV,hc,hd⟩ := Finset.mem_filter.mp hi
  rw [movingIdeal_valuation P hp hinj c d V i,hc,hd,if_pos hiV]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem forcingIdeal_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (forcingIdeal P c d V) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    let : (P i).IsMaximal := (Ideal.isPrime_of_prime (hp i)).isMaximal (hp i).ne_zero
    let : (P j).IsMaximal := (Ideal.isPrime_of_prime (hp j)).isMaximal (hp j).ne_zero
    exact (Ideal.isCoprime_of_isMaximal (hinj.ne hij)).isRelPrime
  · intro i hi
    exact (hp i).squarefree

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_prime_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Q : Ideal O)
    (hQ : Q ∈ normalizedFactors (forcingIdeal P c d V)) :
    ∃ i ∈ forcingSet c d V, Q = P i := by
  have hf : normalizedFactors (forcingIdeal P c d V) =
      (forcingSet c d V).val.map P := by
    apply normalizedFactors_prod_of_prime
    intro R hR
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hR
    exact hp i
  rw [hf] at hQ
  obtain ⟨i,hi,hPi⟩ := Multiset.mem_map.mp hQ
  exact ⟨i,hi,hPi.symm⟩

omit [DecidableEq ι] in
theorem movingElement_span (p : ι → O) (c d : ι → ℕ) (V : Finset ι) :
    Ideal.span {movingElement p c d V} = movingIdeal (fun i => Ideal.span {p i}) c d V := by
  simp only [movingElement,movingIdeal,Ideal.span_singleton_pow,
    Ideal.prod_span_singleton,Ideal.span_singleton_mul_span_singleton]

end SevenEighths.CenteredMomentForcing

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Smooth
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentSmooth
open FourierBridge EisensteinSchwartzPoisson

theorem logPhase_norm_ratio (q X θ : ℝ) (hq : 0 < q) (hX : 0 < X) :
    logPhase θ (-Real.log (q / X)) =
      logPhase θ (Real.log X) * (q : ℂ) ^ (Complex.I * (-(2 * Real.pi * θ))) := by
  have hlog : -Real.log (q / X) = Real.log X + -Real.log q := by
    rw [Real.log_div hq.ne' hX.ne']
    ring
  rw [hlog, logPhase_add]
  congr 1
  have hθ : (-(2 * Real.pi * θ)) / (2 * Real.pi) = -θ := by
    have hp := Real.pi_ne_zero
    field_simp
  have hn := CenteredMomentLattice.logPhase_eq_normPower (-(2 * Real.pi * θ)) q hq
  rw [hθ] at hn
  push_cast at hn
  rw [← hn]
  unfold logPhase
  congr 1
  push_cast
  ring

open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentSmooth
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

end SevenEighths.CenteredMomentRankinRadical

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

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

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

theorem heightCoeff_add (τ : Character) (I : Ideal O) (hI : I≠0) (t v : ℝ) :
    heightCoeff τ (t+v) I=heightCoeff τ t I*(Ideal.absNorm I:ℂ)^(Complex.I*v) := by
  have hn : (Ideal.absNorm I:ℂ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [heightCoeff,Complex.ofReal_add,mul_add,Complex.cpow_add _ _ hn]
  ring

theorem heightCoeff_phase (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X))=
      logPhase θ (Real.log X)*heightCoeff τ (t-2*Real.pi*θ) I := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [logPhase_norm_ratio _ X θ hn hX,sub_eq_add_neg,heightCoeff_add τ I hI]
  push_cast
  ring

theorem rootProfile_apply (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootProfile V hVc hVs u=rootWindow V u := by
  change V u*(Real.exp (-u/2):ℂ)=_
  rw [rootWindow,← Real.exp_half,show -u/2=-(u/2) by ring,Real.exp_neg,
    Complex.ofReal_inv,div_eq_mul_inv]
  ring

theorem columnDensity_moments (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (J : ℕ) :
    Integrable (fun w : ℝ => (1+‖w‖)^J*‖columnDensity V hVc hVs w‖) :=
  JointLogSeparation.weighted_schwartz_integrable _ J

theorem rootWindow_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootWindow V u=∫ w : ℝ,logPhase w u*columnDensity V hVc hVs w := by
  rw [← rootProfile_apply V hVc hVs u,schwartz_log_inversion]
  apply integral_congr_ae
  filter_upwards [] with w
  congr 2
  simp only [Real.inner_apply]
  push_cast
  ring

theorem phase_combine (w θ u : ℝ) :
    logPhase w u*logPhase θ (-u)=logPhase (θ-w) (-u) := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem height_column_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) I := by
  rw [columnPhase,rootWindow_integral V hVc hVs,← mul_assoc,← integral_const_mul,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with w
  calc
    _ = columnDensity V hVc hVs w*(heightCoeff τ t I*
      (logPhase w (Real.log ((Ideal.absNorm I:ℝ)/X))*
        logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by ring
    _ = _ := by
      rw [phase_combine,heightCoeff_phase τ I hI t (θ-w) X hX,
        show t-2*Real.pi*(θ-w)=t+2*Real.pi*(w-θ) by ring]
      ring

theorem height_column_integrable (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) := by
  have he (w : ℝ) : logPhase (θ-w) (Real.log X)*heightCoeff τ (t+2*Real.pi*(w-θ)) I=
      heightCoeff τ t I*logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)) := by
    rw [heightCoeff_phase τ I hI t (θ-w) X hX]
    congr 2
    ring
  have hfun : (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) =
      (fun w : ℝ => columnDensity V hVc hVs w*(heightCoeff τ t I*
        logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by
    funext w
    rw [mul_assoc,he w]
  rw [hfun]
  apply ((columnDensity V hVc hVs).integrable.norm.const_mul ‖heightCoeff τ t I‖).mono'
  · have hp := (logPhase_continuous_left (-Real.log ((Ideal.absNorm I:ℝ)/X))).comp
      (show Continuous (fun w : ℝ => θ-w) from continuous_const.sub continuous_id)
    exact ((columnDensity V hVc hVs).continuous.mul (hp.const_mul _)).aestronglyMeasurable
  · filter_upwards [] with w
    simp only [norm_mul,logPhase_norm,mul_one]
    exact le_of_eq (mul_comm _ _)

end SevenEighths.CenteredMomentHeckeColumnWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem heightCost_pos (t θ : ℝ) : 0<heightCost t θ := by
  unfold heightCost
  positivity

theorem norm_height_shift (t θ w : ℝ) :
    1+‖t+2*Real.pi*(w-θ)‖≤heightCost t θ*(1+‖w‖) := by
  have hπ : 0≤2*Real.pi := by positivity
  have hn := norm_add_le t (2*Real.pi*(w-θ))
  rw [norm_mul,Real.norm_of_nonneg hπ] at hn
  have hs := norm_sub_le w θ
  have hr : 1+‖t+2*Real.pi*(w-θ)‖≤1+‖t‖+2*Real.pi*‖θ‖+2*Real.pi*‖w‖ := by
    nlinarith
  have hb : 1≤1+‖t‖+2*Real.pi*‖θ‖ := by
    nlinarith [norm_nonneg t,mul_nonneg hπ (norm_nonneg θ)]
  have hw : 0≤2*Real.pi*‖w‖ := by positivity
  calc
    _ ≤ (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi*‖w‖) := by nlinarith
    _ ≤ _ := by
      unfold heightCost
      rw [mul_assoc (1+‖t‖+2*Real.pi*‖θ‖) (1+2*Real.pi) (1+‖w‖)]
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hb)
      nlinarith [norm_nonneg w,Real.pi_pos]

end SevenEighths.CenteredMomentHeckeWindowEnergy

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

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentSupport UniqueFactorizationMonoid
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

lemma common_prime_dvd_left (C D:Ideal O) (P:CommonIndex C D) : P.val∣C :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma common_prime_prime (C D:Ideal O) (hC:Supported C) (P:CommonIndex C D) :
    Prime (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

end SevenEighths.CenteredMomentSecondExceptionalCount

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PlainWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentPlainWindowEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem plain_column_integral {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    rowPolynomial S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i})) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold rowPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul,← height_column_integral V hVc hVs τ _ (ha i).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem plain_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}))
  convert (preTransparency := .instances) integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SevenEighths.CenteredMomentPlainWindowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalSourceShell
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalSourceShell
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalAllocationShell
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma profileMass_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):0≤profileMass s v p q J:=by
  unfold profileMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
    (slotControl_nonneg s)) (slotControl_nonneg v)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end SevenEighths.CenteredMomentExceptionalSourceShell

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowPair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWindowPair
open CenteredMomentPlainWindowEnergy CenteredMomentRowNorm CenteredMomentSmooth
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem paired_integrals {κ:Type*}(rows:Finset κ)(f g:κ→ℝ→ℂ)
    (hf:∀z∈rows,Integrable (f z))(hg:∀z∈rows,Integrable (g z))
    (a b:ℝ→ℝ)(ha:Integrable a)(hb:Integrable b)
    (_ha0:∀u,0≤a u)(_hb0:∀v,0≤b v)(E:ℝ)(_hE:0≤E)
    (hpair:∀u v,∑z∈rows,‖f z u‖*‖g z v‖≤E*a u*b v):
    (∑z∈rows,‖∫u,f z u‖*‖∫v,g z v‖)≤E*(∫u,a u)*(∫v,b v):=by
  have hinner (u:ℝ):
      (∑z∈rows,‖f z u‖*‖∫v,g z v‖)≤E*a u*(∫v,b v):=by
    calc
      _≤∑z∈rows,‖f z u‖*(∫v,‖g z v‖):=
        Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm _) (norm_nonneg _))
      _=∫v,∑z∈rows,‖f z u‖*‖g z v‖:=by
        rw [integral_finsetSum _ (fun z hz=>(hg z hz).norm.const_mul _)]
        simp only [integral_const_mul]
      _≤∫v,E*a u*b v:=integral_mono
        (integrable_finsetSum rows (fun z hz=>(hg z hz).norm.const_mul _))
        (hb.const_mul _) (fun v=>hpair u v)
      _=E*a u*(∫v,b v):=integral_const_mul _ _
  calc
    _≤∑z∈rows,(∫u,‖f z u‖)*‖∫v,g z v‖:=
      Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_right
        (norm_integral_le_integral_norm _) (norm_nonneg _))
    _=∫u,∑z∈rows,‖f z u‖*‖∫v,g z v‖:=by
      rw [integral_finsetSum _ (fun z hz=>(hf z hz).norm.mul_const _)]
      simp only [integral_mul_const]
    _≤∫u,E*a u*(∫v,b v):=integral_mono
      (integrable_finsetSum rows (fun z hz=>(hf z hz).norm.mul_const _))
      ((ha.const_mul E).mul_const _) hinner
    _=E*(∫u,a u)*(∫v,b v):=by rw [integral_mul_const,integral_const_mul]

end SevenEighths.CenteredMomentExceptionalWindowPair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalIndexedWindow
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalIndexedWindow
open CenteredMomentExceptionalWindowPair CenteredMomentPlainWindowEnergy
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem indexed_plain_window_pair {κ α β:Type*}
    (rows:Finset κ)(row:κ→O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:κ→α→ℂ)(d:κ→β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑z∈rows,
      ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)‖*
      ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑z∈rows,
      ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) (row z)‖*
      ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) (row z)‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  let f:=fun z:κ=>fun u:ℝ=>columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁-u) (Real.log X)*
    rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)
  let g:=fun z:κ=>fun v:ℝ=>columnDensity V₂ hc₂ hs₂ v*logPhase (θ₂-v) (Real.log Y)*
    rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)
  have hf (z:κ):Integrable (f z):=plain_column_integrable S a ha (c z) τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ (row z)
  have hg (z:κ):Integrable (g z):=plain_column_integrable T b hb (d z) τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ (row z)
  have hh:=paired_integrals rows f g (fun z _=>hf z) (fun z _=>hg z)
    (fun u=>(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun v=>(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun u=>by positivity) (fun v=>by positivity) E hE ?_
  · have hfEq (z:κ):
        (∫u:ℝ,f z u)=rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
          columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) (row z):=
        (plain_column_integral S a ha (c z) τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ (row z)).symm
    have hgEq (z:κ):
        (∫v:ℝ,g z v)=rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
          columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) (row z):=
        (plain_column_integral T b hb (d z) τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ (row z)).symm
    simpa only [hfEq,hgEq] using hh
  · intro u v
    simp only [f,g,norm_mul,logPhase_norm,mul_one]
    calc
      _=(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
        (∑z∈rows,
          ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)‖*
          ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)‖):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _≤(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
          (E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):=
        mul_le_mul_of_nonneg_left (hpair u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _=_:=by ring

end SevenEighths.CenteredMomentExceptionalIndexedWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeWindow
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWholeWindow
open CenteredMomentExceptionalIndexedWindow CenteredMomentPlainWindowEnergy
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem rowPolynomial_factor {α:Type*}(S:Finset α)(a:α→O)(c:α→ℂ)(v:ℂ)(z:O):
    rowPolynomial S a (fun i=>v*c i) z=v*rowPolynomial S a c z:=by
  simp only [rowPolynomial,Finset.mul_sum,mul_assoc]

theorem whole_plain_window_pair {γ α β:Type*}
    (Ds:Finset γ)(μ:γ→ℂ)(rows:Finset O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:γ→α→ℂ)(d:γ→β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖rowPolynomial S a (fun i=>c L i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
      ‖rowPolynomial T b (fun j=>d L j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖rowPolynomial S a (fun i=>c L i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) z‖*
      ‖rowPolynomial T b (fun j=>d L j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  have hh:=indexed_plain_window_pair (Ds×ˢrows) (fun x:γ×O=>x.2) S T a b ha hb
    (fun x i=>μ x.1*c x.1 i) (fun x j=>d x.1 j) τ₁ τ₂ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [mul_assoc,rowPolynomial_factor,norm_mul,
      Finset.sum_product,Finset.mul_sum,mul_assoc] using hh
  · intro u v
    simpa only [mul_assoc,rowPolynomial_factor,norm_mul,
      Finset.sum_product,Finset.mul_sum,mul_assoc] using hpair u v

end SevenEighths.CenteredMomentExceptionalWholeWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentCommonWindowColumn
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentCommonWindowColumn.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
theorem coefficient_polynomial (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t:ℝ)(z:O):
    rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
      (fun I=>coefficient s C hC R seed L I*heightCoeff η t I) z=
      normalizedColumn (withHeight s η t) C hC R seed L z:=by
  unfold normalizedColumn sourceColumn
  dsimp only [withHeight,Input.pools,columns]
  simp only [coefficient,mul_assoc,rowPolynomial_factor,Input.pools,columns]
  rfl

theorem sourceGenerator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

omit [DecidableEq ι] in
theorem whole_window_pair (s v:Input ι)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(Ds:Finset (Ideal O))(μ:Ideal O→ℂ)(rows:Finset O)
    (η τ:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u w:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖normalizedColumn (withHeight s η (t₁+2*Real.pi*(u-θ₁))) C hC R seed L z‖*
      ‖normalizedColumn (withHeight v τ (t₂+2*Real.pi*(w-θ₂))) D hD R seed L z‖)≤
        E*(1+‖u‖)^J₁*(1+‖w‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖windowColumn s C hC R seed L η t₁ θ₁ X V₁ z‖*
      ‖windowColumn v D hD R seed L τ t₂ θ₂ Y V₂ z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫w:ℝ,(1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖):=by
  have hh:=whole_plain_window_pair Ds μ rows Finset.univ Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator (columns v D hD))
    (sourceGenerator_supported _) (sourceGenerator_supported _)
    (coefficient s C hC R seed) (coefficient v D hD R seed) η τ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [sourceGenerator_span,windowColumn] using hh
  · intro u w
    simpa only [sourceGenerator_span,coefficient_polynomial] using hpair u w

end SevenEighths.CenteredMomentCommonWindowColumn

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonAsymmetric
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma profileMass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):0≤profileMass R s v p q J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s
  have hv:=slotControl_nonneg v
  unfold profileMass
  positivity

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonHeight
namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentExceptionalAmplitudePair CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentHeckeWindowEnergy
open HeckeFamily CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
universe u

theorem mass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ)) {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):
    0≤ mass R s v p q t₁ t₂ θ₁ θ₂ J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s.toData
  have hv:=slotControl_nonneg v.toData
  have ht₁:=(heightCost_pos t₁ θ₁).le
  have ht₂:=(heightCost_pos t₂ θ₂).le
  unfold mass
  positivity

theorem shifted_mass {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(η τ:Character)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂ u w:ℝ)(J:ℕ):
    profileMass R (withHeight s η (t₁+2*Real.pi*(u-θ₁))).toData
      (withHeight v τ (t₂+2*Real.pi*(w-θ₂))).toData p q J≤
      mass R s v p q t₁ t₂ θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J:=by
  have hp:=pow_le_pow_left₀ (by positivity) (norm_height_shift t₁ θ₁ u) J
  have hq:=pow_le_pow_left₀ (by positivity) (norm_height_shift t₂ θ₂ w) J
  have hh:=mul_le_mul hp hq (by positivity)
    (pow_nonneg (mul_nonneg (heightCost_pos t₁ θ₁).le (by positivity)) _)
  have hcontrol:=mul_nonneg (Profiles.control_nonneg p R) (Profiles.control_nonneg q R)
  have hs:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hcontrol)
        (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
      (Real.sqrt_nonneg (volume v.toData))
  convert (preTransparency := .instances) hs using 1
  · dsimp only [profileMass,withHeight,slotControl,volume]
    ring
  · simp only [mass,mul_pow]
    ring
end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FixedQForcingCount
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedQForcingCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentForcing CenteredMomentChildRows CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSupport
open CenteredMomentSourceRow
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma prime_product_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) : Squarefree (∏ i ∈ S, P i) := by
  simpa [forcingIdeal, forcingSet] using
    forcingIdeal_squarefree P hp hinj (fun _ => 1) (fun _ => 1) S

omit [Fintype ι] [DecidableEq ι] in
lemma prime_product_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (S : Finset ι) (R : Ideal O) (hR : R ∈ normalizedFactors (∏ i ∈ S, P i)) :
    ∃ i ∈ S, R = P i := by
  simpa [forcingIdeal, forcingSet] using
    forcing_prime_mem P hp (fun _ => 1) (fun _ => 1) S R (by
      simpa [forcingIdeal, forcingSet] using hR)

omit [Fintype ι] [DecidableEq ι] in
lemma goodIdeal_squarefree (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (goodIdeal Q P c d V) :=
  prime_product_squarefree P hp hinj _

omit [Fintype ι] [DecidableEq ι] in
lemma goodIdeal_ne_zero (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : goodIdeal Q P c d V ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)

lemma good_valuation_two (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι)
    (hi : i ∈ goodSet Q P c d V) :
    CenteredExceptionalCount.valuation (movingIdeal P c d V) (P i) = 2 :=
  forcing_valuation_two P hp hinj c d V i (Finset.mem_filter.mp hi).1

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_split (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) :
    goodIdeal Q P c d V * excludedIdeal Q P c d V = forcingIdeal P c d V := by
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

lemma prime_dvd_of_not_coprime (Q P : Ideal O) (hP : Prime P) (h : ¬IsCoprime Q P) : P ∣ Q := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hs : Q ⊔ P ≠ ⊤ := by simpa only [Ideal.isCoprime_iff_sup_eq] using h
  have he : P = Q ⊔ P := Ideal.IsMaximal.eq_of_le inferInstance hs le_sup_right
  exact Ideal.dvd_iff_le.mpr (le_sup_left.trans_eq he.symm)

omit [Fintype ι] [DecidableEq ι] in
lemma excludedIdeal_dvd_radical (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) : excludedIdeal Q P c d V ∣ commonRadical Q Q := by
  apply (CenteredMomentDivisorAllocation.squarefree_dvd_iff _ _
    (prime_product_squarefree P hp hinj _)).mpr
  intro R hR
  obtain ⟨i,hi,rfl⟩ := prime_product_mem P hp _ R (Multiset.mem_toFinset.mp hR)
  have hd := prime_dvd_of_not_coprime Q (P i) (hp i) (Finset.mem_filter.mp hi).2
  have hm : P i ∈ IdealMobiusDivisorSum.primeSupport Q := by
    simpa only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff hQ,
      hp i, true_and] using hd
  exact Finset.dvd_prod_of_mem id (Finset.mem_inter.mpr ⟨hm,hm⟩)

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_dvd_good_mul_radical (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) :
    forcingIdeal P c d V ∣ goodIdeal Q P c d V * commonRadical Q Q := by
  rw [←forcing_split Q P c d V]
  exact mul_dvd_mul_left _ (excludedIdeal_dvd_radical Q hQ P hp hinj c d V)

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_norm_le (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) :
    (Ideal.absNorm (forcingIdeal P c d V) : ℝ) ≤
      (Ideal.absNorm (goodIdeal Q P c d V) : ℝ) * Ideal.absNorm (commonRadical Q Q) := by
  have hd := map_dvd Ideal.absNorm (forcing_dvd_good_mul_radical Q hQ P hp hinj c d V)
  have hn : (goodIdeal Q P c d V) * commonRadical Q Q ≠ 0 :=
    mul_ne_zero (goodIdeal_ne_zero Q P hp c d V) (commonRadical_ne_zero Q Q)
  have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) hd
  exact_mod_cast (show Ideal.absNorm (forcingIdeal P c d V) ≤
    Ideal.absNorm (goodIdeal Q P c d V) * Ideal.absNorm (commonRadical Q Q) by simpa using hh)

lemma fixed_radical_power_loss (Z M f g r : ℝ) (hZ : 1 < Z)
    (hf : 0 < f) (hg : 0 < g) (hr : 0 < r) (hfg : f ≤ g*r) :
    Z ^ ((M-4*Real.logb Z g)/6) ≤
      r^(2/3:ℝ) * Z^((M-4*Real.logb Z f)/6) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.logb_le_logb_of_le hZ hf hfg
  rw [Real.logb_mul hg.ne' hr.ne'] at hl
  calc
    _ ≤ Z^(Real.logb Z r*(2/3)+(M-4*Real.logb Z f)/6) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = _ := by
      rw [Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hr]

theorem actual_forcing_exceptional_count_fixedQ (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι)
    (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m e : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (he : elementCoeff η e ≠ 0) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      goodLambda ∉ Ideal.span {p i} ∧ (2 : O) ∉ Ideal.span {p i} ∧
      Ideal.span {p i} ∣ Ideal.span {e})
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr * Z ^ M) :
    (rows.card : ℝ) ≤ (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ) *
      (768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card * Cr^(1/6:ℝ) *
        Z^((M-4*Real.logb Z (Ideal.absNorm
          (forcingIdeal (fun i => Ideal.span {p i}) c d V):ℝ))/6)) := by
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let G := goodIdeal Q P c d V
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  have hG0 : G ≠ 0 := goodIdeal_ne_zero Q P hp c d V
  have hGn : (0:ℝ) < Ideal.absNorm G := CenteredExceptionalCount.norm_pos hG0
  have hb := separated_exceptional_count η χ Q hQ0 hQ hQ72
    m (movingElement p c d V) e hm hA hmLam hm2 he rows hrows hex G
    (goodIdeal_squarefree Q P hp hinj c d V) (by
      intro R hR
      obtain ⟨i,hi,rfl⟩ := prime_product_mem P hp (goodSet Q P c d V) R hR
      obtain ⟨hif,hQi⟩ := Finset.mem_filter.mp hi
      obtain ⟨hl,h2,hd⟩ := hgood i hif
      refine ⟨hl,h2,hQi,hd,?_⟩
      rw [movingElement_span,good_valuation_two Q P hp hinj c d V i hi])
    Z Cr M (2*Real.logb Z (Ideal.absNorm G:ℝ)) (zero_lt_one.trans hZ) hCr (by
      rw [show (2*Real.logb Z (Ideal.absNorm G:ℝ))/2=Real.logb Z (Ideal.absNorm G:ℝ) by ring,
        Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hGn]) hN
  have hb' : (rows.card:ℝ) ≤ 768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm G:ℝ))/6) := by
    have heq : (M-2*(2*Real.logb Z (Ideal.absNorm G:ℝ)))/6 =
        (M-4*Real.logb Z (Ideal.absNorm G:ℝ))/6 := by ring
    simpa only [heq] using hb
  have hf : (0:ℝ) < Ideal.absNorm (forcingIdeal P c d V) := by
    apply CenteredExceptionalCount.norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  have hr : (0:ℝ) < Ideal.absNorm (commonRadical Q Q) :=
    CenteredExceptionalCount.norm_pos (commonRadical_ne_zero Q Q)
  have hs := fixed_radical_power_loss Z M _ _ _ hZ hf hGn hr
    (forcing_norm_le Q hQ0 P hp hinj c d V)
  apply hb'.trans
  calc
    _ ≤ (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        ((Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal P c d V):ℝ))/6)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem actual_canonical_exceptional_count_fixedQ (η : Character) (χ : RayFourExpansion.RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hη : idealCoeff η C ≠ 0)
    (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^M) :
    (rows.card:ℝ) ≤ (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D => P.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6)) := by
  have he : elementCoeff η (primaryGenerator C) ≠ 0 := by
    rw [←idealCoeff_span η (supported_primaryGenerator_ne_zero C hC),primary_span_supported C hC]
    exact hη
  have hinj : Function.Injective (fun P:CommonIndex C D => Ideal.span {commonPrime C D P}) := by
    simpa only [commonPrime_span C D hC] using
      (Subtype.val_injective : Function.Injective (fun P:CommonIndex C D => P.val))
  have hb := actual_forcing_exceptional_count_fixedQ (commonPrime C D) (common_prime_prime C D hC) hinj
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U) η χ
    Q hQ0 hQ hQ72 m (primaryGenerator C) hm hmLam hm2 he rows hrows hex (by
      intro P _
      rw [commonPrime_span C D hC P]
      refine ⟨common_good C D hC P,CanonicalRowCompletion.good_odd_prime_two_not_mem _
        (common_odd C D hC P),?_⟩
      rw [primary_span_supported C hC]
      exact common_prime_dvd_left C D P) Z Cr M hZ hCr hN
  simpa only [commonPrime_span C D hC] using hb

end SevenEighths.CenteredMomentFixedQForcingCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQCanonical
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFixedQForcingCount CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_canonical_bound (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤ s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤ s.X₁ → Z^rLeft≤ s.X₂ → Z^rLeft≤ s.Y₁ → Z^rLeft≤ s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
            (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_better_side wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  let qcost:ℝ:=(Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)
  have hqcost:0<qcost:=by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero Q Q))
  refine ⟨K*qcost,mul_pos hK hqcost,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hc:=actual_canonical_exceptional_count_fixedQ η₀ χ C D hC U Q hQ hQtop hQ72 hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  have hb:=hZ.2 s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  let F:ℝ:=profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm)
  have hF:0≤F:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg Sprofile _ _ _ _ _) (frozenProfile_nonneg _))
    (frozenProfile_nonneg _)) (by positivity)
  let e:ℝ:=2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
    (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)
  let f:ℝ:=(M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6
  have hz:=zero_lt_one.trans hZ.1
  apply hb.trans
  calc
    _≤K*(qcost*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f))*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F:=by
      apply mul_le_mul_of_nonneg_right _ hF
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hc hK.le
    _=_:=by
      have hpow:Z^(f+e)=Z^f*Z^e:=Real.rpow_add hz _ _
      change K*(qcost*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f))*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F=(K*qcost)*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^(f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*((C.absNorm:ℝ)*D.absNorm)^θ*F
      rw [show f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)=f+e by dsimp [e];ring,hpow]
      ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQWindow
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_common_window_oai (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤ s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤ s.X₁ → Z^rLeft≤ s.X₂ → Z^rLeft≤ s.Y₁ → Z^rLeft≤ s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀θ₁ θ₂ X Y:ℝ,0<X → 0<Y →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L s.η s.t θ₁ X logAnnulus z‖*
        ‖windowColumn v D hD R seed L v.η v.t θ₂ Y logAnnulus z‖)≤
        K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
              (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))*
          mass Sprofile s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_canonical_bound wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hη m hm hml hm2 hex Cr M hCr hN θ₁ θ₂ X Y hX hY Ds hDs
  let F:=K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
              (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg v)) (by positivity))
  have hh:=whole_window_pair s v C D hC hD R seed Ds (fun L=>(moebius L:ℂ)) rows
    s.η v.η s.t v.t θ₁ θ₂ X Y hX hY logAnnulus logAnnulus
    logAnnulus_compact logAnnulus_compact logAnnulus_smooth logAnnulus_smooth
    J J (F*mass Sprofile s v p q s.t v.t θ₁ θ₂ J)
    (mul_nonneg hF (mass_nonneg Sprofile s v p q s.t v.t θ₁ θ₂ J)) ?_
  · simpa only [F,pow_two,mul_assoc] using hh
  intro u w
  have hb:=hZ.2 (withHeight s s.η (s.t+2*Real.pi*(u-θ₁)))
    (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))) p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂
    C D hC hD R seed hR hsC hsD rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
    rows hn hsEx hvEx hsCond hvCond η₀ χ U hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hm:=shifted_mass Sprofile s v s.η v.η p q s.t v.t θ₁ θ₂ u w J
  apply hb.trans
  calc
    _=F*profileMass Sprofile (withHeight s s.η (s.t+2*Real.pi*(u-θ₁))).toData
        (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))).toData p q J:=by
      dsimp only [F,frozenProfile,withHeight]
      ring
    _≤F*(mass Sprofile s v p q s.t v.t θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ.actual_canonical_common_window_oai.{u} := @OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ.actual_canonical_common_window_oai.{u}
