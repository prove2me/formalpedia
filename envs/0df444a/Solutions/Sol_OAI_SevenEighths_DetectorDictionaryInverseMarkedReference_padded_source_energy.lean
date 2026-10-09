-- Prove2me | solution 1 for OAI.SevenEighths.DetectorDictionaryInverseMarkedReference.padded_source_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:31:13.454785+00:00
-- url     : https://prove2.me/submissions/4b1b2ea9-4997-45c4-a8a9-c3467b70e7c6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Theorems.Thm_OAI_SevenEighths_InverseInitialResidualUniformEnergy_original_residual_uniform_energy

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
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

namespace ActualEisensteinCubic

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
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

open scoped BigOperators Classical

namespace FirstCauchyArithmetic

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

end FirstCauchyArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
namespace SecondPassIntegration
open JointLogSeparation FourierBridge

lemma logPhase_conjugate (t x : ℝ) : star (logPhase t x) = logPhase (-t) x := by
  unfold logPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring

end SecondPassIntegration

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Overlap
namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

section Moebius

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem moebius_squarefree_sq {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

theorem moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]

theorem moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by
  have hμ : (moebius n₀ : ℂ) = (moebius (n₀ * P₀) : ℂ) * (moebius P₀ : ℂ) := by
    exact_mod_cast moebius_overlap_recovery hnP hP
  rw [hjn.moebius_mul, Int.cast_mul, map_mul, map_mul, map_mul, hμ]
  ring

end Moebius

end SevenEighths.InverseMoment

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

lemma idealBall_card (H : ℝ) (hH : 0 ≤ H) :
    ((idealBall H).card : ℝ) ≤ 128*H := by
  by_cases hs : (idealBall H).Nonempty
  · obtain ⟨I,hI⟩ := hs
    have hI := (mem_idealBall H I).mp hI
    have hn : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    exact DescentFiberCost.finite_ideal_count_real _ H (hn.trans hI.2)
      (fun J hJ => ((mem_idealBall H J).mp hJ).1)
      (fun J hJ => ((mem_idealBall H J).mp hJ).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

open CenteredMomentAddedZeroUniform

end SevenEighths.CenteredMomentSourceMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseAssignedCount
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.DetectorDictionaryInverseAssignedCount
local notation "O" => ActualEisensteinCubic.O

theorem assignedConstant_pos (K : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    0 < assignedConstant K b := by
  unfold assignedConstant
  positivity

theorem list_card_le (L : Finset (Ideal O)) {H : ℝ} (hH : 0 ≤ H)
    (hL : ∀ I ∈ L, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H) :
    (L.card : ℝ) ≤ 128*H := by
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (t :=
    CenteredMomentSourceMass.idealBall H) ?_))
    (CenteredMomentSourceMass.idealBall_card H hH)
  intro I hI
  exact (CenteredMomentSourceMass.mem_idealBall H I).mpr (hL I hI)

theorem assigned_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples L).card : ℝ) ≤ assignedConstant K b * U^(∑ i, ell i) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hbase : 1 ≤ 128*b := by linarith
  simp only [assignedTuples, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i, ((L i).card : ℝ)) ≤ ∏ i, 128*(b*U^(ell i)) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => list_card_le (L i) (by positivity) (hL i))
    _ = (128*b)^(Fintype.card ι) * U^(∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hUp]
      simp
    _ ≤ assignedConstant K b * U^(∑ i, ell i) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hK)
        (Real.rpow_nonneg hUp.le _)

theorem assignedCoefficient_norm_le_one {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (a : ι → Ideal O → ℂ)
    (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (q : ι → Ideal O) (hq : q ∈ assignedTuples L) :
    ‖assignedCoefficient a q‖ ≤ 1 := by
  rw [assignedCoefficient, norm_prod]
  simpa using Finset.prod_le_prod (fun i _ => norm_nonneg (a i (q i)))
    (fun i _ => ha i (q i) ((mem_assignedTuples L q).mp hq i))

theorem restricted_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤
      assignedConstant K b * U^(∑ i, ell i) := by
  calc
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤ ∑ _q ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => assignedCoefficient_norm_le_one L a ha q (hT hq))
    _ = (T.card : ℝ) := by simp
    _ ≤ ((assignedTuples L).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hT)
    _ ≤ _ := assigned_card_le K hb hU hK ell L hL

theorem restricted_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) * U^(-(∑ i, ell i)) ≤
      assignedConstant K b := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (assignedConstant K b * U^(∑ i, ell i)) * U^(-(∑ i, ell i)) :=
      mul_le_mul_of_nonneg_right (restricted_mass_le K hb hU hK ell L hL a ha T hT)
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hUp]; simp

theorem restricted_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b := by
  rw [← Finset.sum_mul]
  exact restricted_normalized_mass_le K hb hU hK ell L hL a ha T hT

theorem assigned_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1) :
    (∑ q ∈ assignedTuples L, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b :=
  restricted_sum_normalized_le K hb hU hK ell L hL a ha _ (Finset.Subset.refl _)

end SevenEighths.DetectorDictionaryInverseAssignedCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlap
namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
open UniqueFactorizationMonoid

namespace SevenEighths.InverseInitialOverlap

theorem mem_original {S : Finset (Ideal O)} {P j n : Ideal O} :
    n ∈ original S P j ↔ n ∈ S ∧ Squarefree n ∧ gcd n P = j := by
  simp only [original, Finset.mem_filter]

theorem residual_mul {P j : Ideal O} (hj : j ∣ P) : j * residual P j = P :=
  idealQuotient_mul hj

theorem residual_squarefree {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) :
    Squarefree (residual P j) :=
  hP.squarefree_of_dvd (idealQuotient_dvd hj)

theorem quotient_mul_cancel {D H : Ideal O} (hD : D ≠ 0) :
    idealQuotient D (D * H) = H :=
  mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D H))

theorem column_properties {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hn : Squarefree n) (hg : gcd n P = j) :
    Squarefree (column P j n) ∧ IsCoprime (column P j n) j ∧
      residual P j ∣ column P j n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hHP : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have hHj := hHP.mono (dvd_refl _) hj
  have hHP0 := hHP.mono (dvd_refl _) (idealQuotient_dvd hj)
  have hJP0 : IsCoprime j (residual P j) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (j * residual P j) by rw [residual_mul hj]; exact hP)).1
  refine ⟨squarefree_mul_iff.mpr ⟨hHP0.isRelPrime,
    hn.squarefree_of_dvd (idealQuotient_dvd hjn), residual_squarefree hP hj⟩,
    hHj.mul_left hJP0.symm, dvd_mul_left _ _⟩

theorem reconstruct_column {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hg : gcd n P = j) : reconstruct P j (column P j n) = n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hP0 := (residual_squarefree hP hj).ne_zero
  unfold reconstruct column
  rw [mul_comm (idealQuotient j n), quotient_mul_cancel hP0, idealQuotient_mul hjn]

theorem reconstruct_properties {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hc : Squarefree c) (hcj : IsCoprime c j) (hPc : residual P j ∣ c) :
    Squarefree (reconstruct P j c) ∧ gcd (reconstruct P j c) P = j := by
  let H := idealQuotient (residual P j) c
  have hHc : H ∣ c := idealQuotient_dvd hPc
  have hHj : IsCoprime H j := hcj.mono hHc (dvd_refl _)
  have hHP0 : IsCoprime H (residual P j) :=
    (ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (residual P j * H) by rw [idealQuotient_mul hPc]; exact hc)).1).symm
  have hHP : IsCoprime H P := by
    rw [← residual_mul hj]
    exact hHj.mul_right hHP0
  exact ⟨squarefree_mul_iff.mpr ⟨hHj.symm.isRelPrime,
    hP.squarefree_of_dvd hj, hc.squarefree_of_dvd hHc⟩,
    gcd_mul_of_coprime_divisor j H P hj hHP⟩

theorem column_reconstruct {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) : column P j (reconstruct P j c) = c := by
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hj
  unfold column reconstruct
  rw [quotient_mul_cancel hj0, mul_comm, idealQuotient_mul hPc]

theorem mem_columns {S : Finset (Ideal O)} {P j c : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    c ∈ columns S P j ↔ Squarefree c ∧ IsCoprime c j ∧
      residual P j ∣ c ∧ reconstruct P j c ∈ S := by
  constructor
  · intro hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hnS, hn, hg⟩ := mem_original.mp hn
    obtain ⟨hcs, hcj, hPc⟩ := column_properties hP hj hn hg
    exact ⟨hcs, hcj, hPc, by rwa [reconstruct_column hP hj hg]⟩
  · rintro ⟨hc, hcj, hPc, hnS⟩
    obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hc hcj hPc
    exact Finset.mem_image.mpr ⟨reconstruct P j c,
      mem_original.mpr ⟨hnS, hn, hg⟩, column_reconstruct hP hj hPc⟩

theorem column_injOn (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    Set.InjOn (column P j) (original S P j) := by
  intro n hn m hm he
  have hn' := reconstruct_column hP hj (mem_original.mp hn).2.2
  have hm' := reconstruct_column hP hj (mem_original.mp hm).2.2
  rw [← hn', ← hm', he]

theorem reconstruct_mul_residual {P j c : Ideal O} (hPc : residual P j ∣ c) :
    reconstruct P j c * residual P j = j * c := by
  unfold reconstruct
  rw [mul_assoc, mul_comm (idealQuotient _ _), idealQuotient_mul hPc]

theorem norm_reconstruct {P j c : Ideal O} (hPc : residual P j ∣ c) :
    Ideal.absNorm (reconstruct P j c) * Ideal.absNorm (residual P j) =
      Ideal.absNorm j * Ideal.absNorm c := by
  simpa only [map_mul] using congrArg Ideal.absNorm (reconstruct_mul_residual hPc)

theorem cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) (X : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / X =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c /
        ((Ideal.absNorm (residual P j) : ℝ) * X) := by
  have h0 : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hn : (Ideal.absNorm (reconstruct P j c) : ℝ) =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c / Ideal.absNorm (residual P j) := by
    apply (eq_div_iff h0).mpr
    exact_mod_cast norm_reconstruct hPc
  rw [hn, div_div]

theorem sum_reconstruct (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (F : Ideal O → ℂ) :
    (∑ n ∈ original S P j, F n) =
      ∑ c ∈ columns S P j, F (reconstruct P j c) := by
  rw [columns, Finset.sum_image (column_injOn S hP hj)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [reconstruct_column hP hj (mem_original.mp hn).2.2]

theorem coefficient_identity (ψ : Ideal O →* ℂ) {P j n : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (hn : Squarefree n) (hg : gcd n P = j) :
    (moebius n : ℂ) * ψ n * ψ P =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2 *
        ((moebius (column P j n) : ℂ) * ψ (column P j n)) := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hH : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have h := InverseMoment.moebius_character_overlap ψ
    (hH.mono (dvd_refl _) hj).symm.isRelPrime
    (hH.mono (dvd_refl _) (idealQuotient_dvd hj)).isRelPrime
    (residual_squarefree hP hj)
  rw [idealQuotient_mul hjn, idealQuotient_mul hj] at h
  change (moebius n : ℂ) * ψ n * ψ P = _
  rw [h]
  unfold column residual
  ring

theorem polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ original S P j,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_reconstruct S hP hj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcs, hcj, hPc, _⟩ := (mem_columns hP hj).mp hc
  obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hcs hcj hPc
  rw [coefficient_identity ψ hP hj hn hg, column_reconstruct hP hj hPc,
    cutoff_argument hP hj hPc]
  ring

theorem sum_original_partition (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (F : Ideal O → ℂ) :
    (∑ n ∈ S.filter Squarefree, F n) =
      ∑ j ∈ idealDivisors P, ∑ n ∈ original S P j, F n := by
  have hmap : ∀ n ∈ S.filter Squarefree, gcd n P ∈ idealDivisors P := by
    intro n _
    exact (mem_idealDivisors hP.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)
  have h := Finset.sum_fiberwise_of_maps_to hmap F
  simpa only [original, Finset.filter_filter] using h.symm

theorem scaled_cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / Z ^ r =
      (((Ideal.absNorm j : ℝ) / Z ^ G) *
        ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
        ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G)) := by
  have hnorm : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hscale : Z ^ G * Z ^ (r + z - 2 * G) = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [cutoff_argument hP hj hPc]
  rw [div_mul_div_comm, div_div_eq_mul_div]
  field_simp [hnorm, (Real.rpow_pos_of_pos hZ r).ne',
    (Real.rpow_pos_of_pos hZ G).ne',
    (Real.rpow_pos_of_pos hZ (r + z - 2 * G)).ne',
    (Real.rpow_pos_of_pos hZ (z - G)).ne']
  linear_combination ((Ideal.absNorm j : ℝ) * Ideal.absNorm c) * hscale

theorem normalization_split {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    Z ^ (-(r + z) / 2) = Z ^ (-G) * Z ^ (-(r + z - 2 * G) / 2) := by
  rw [← Real.rpow_add hZ]
  congr 1
  ring

theorem normalized_polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ original S P j,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
      (Z ^ (-G) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G) / 2) : ℝ) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
  rw [polynomial_fixed_overlap S hP hj ψ a W, normalization_split hZ r z G,
    Complex.ofReal_mul]
  have hs : (∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * Z ^ r))) =
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hPc := ((mem_columns hP hj).mp hc).2.2.1
    rw [← cutoff_argument hP hj hPc, scaled_cutoff_argument hP hj hPc hZ]
  rw [hs]
  ring

theorem normalized_polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S.filter Squarefree,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  rw [sum_original_partition S hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact normalized_polynomial_fixed_overlap S hP
    ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W hZ r z (G j)

theorem sum_moebius_filter (S : Finset (Ideal O)) (F : Ideal O → ℂ) :
    (∑ n ∈ S, (moebius n : ℂ) * F n) =
      ∑ n ∈ S.filter Squarefree, (moebius n : ℂ) * F n := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnf
  have hns : ¬ Squarefree n := fun h => hnf (Finset.mem_filter.mpr ⟨hn, h⟩)
  simp only [moebius_of_not_squarefree hns, Int.cast_zero, zero_mul]

theorem original_normalized_polynomial (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  have hf := sum_moebius_filter S (fun n =>
    ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r))
  simp only [← mul_assoc] at hf
  rw [hf]
  exact normalized_polynomial_all_overlaps S hP ψ a W hZ r z G

end SevenEighths.InverseInitialOverlap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialPoissonBridge
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialPoissonBridge
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open UniqueFactorizationMonoid InverseInitialOverlap
local notation "Eis" => ActualEisensteinCubic.O

theorem idealRowHom_eq_idealSexticRow
    (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    {I : Ideal Eis} (hI : I ∈ F) (u : Eis) :
    idealRowHom u I = idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  conv_lhs => rw [← idealSupport_product_eq F hI (hF I hI).2.1]
  rw [map_prod]
  change (∏ q ∈ idealSupport F I, idealRowHom u q.val) =
    ∏ q ∈ idealSupport F I, CompletedGauss.actualSextic q.val (primePool_good F (pool_good F hF) q)
      (Ideal.Quotient.mk q.val u)
  apply Finset.prod_congr rfl
  intro q hq
  exact idealRowHom_prime u q.val (primePool_good F (pool_good F hF) q)

theorem norm_idealRowHom_four_eq_two (I : Ideal Eis) (hI : Admissible I) (u : Eis) :
    ‖idealRowHom u I‖^4 = ‖idealRowHom u I‖^2 := by
  let F : Finset (Ideal Eis) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have he : J=I := Finset.mem_singleton.mp hJ
    simpa only [he] using hI
  rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_singleton_self I)]
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he := congrArg norm (finiteSquarefreeRow_self_pair
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF)) (idealSupport F I) u)
  simp only [norm_mul,norm_star,←pow_two] at he
  change ‖idealSexticRow F (pool_positive F hF) (pool_good F hF) I u‖^2 = _ at he
  have hp : ∀ x : ℝ, x^4=(x^2)^2 := by intro x; ring
  rw [hp,he]
  unfold rowCoprimeMask
  split_ifs <;> norm_num

theorem heckeIdealCharacter_apply (η : Ideal Eis →* ℂ) (u : Eis) (I : Ideal Eis) :
    heckeIdealCharacter η u I = η I * idealRowHom u I := rfl

theorem originalFixedPolynomial_eq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    originalFixedPolynomial S P j η a W Z r z u =
      overlapPrefactor P j η Z r z G * (idealRowHom u j)^2 *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  have he := normalized_polynomial_fixed_overlap S hP hj (heckeIdealCharacter η u) a W hZ r z G
  change originalFixedPolynomial S P j η a W Z r z u = _ at he
  rw [he]
  simp only [heckeIdealCharacter_apply,
    rowPolynomial,overlapPrefactor,overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem original_normalized_polynomial_hecke_rows
    (S : Finset (Ideal Eis)) {P : Ideal Eis} (hP : Squarefree P)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal Eis → ℝ) (u : Eis) :
    (Z^(-(r+z)/2) : ℝ) * (∑ n ∈ S,
      (moebius n : ℂ)*heckeIdealCharacter η u n*heckeIdealCharacter η u P*
        a n*W ((Ideal.absNorm n : ℝ)/Z^r)) =
      ∑ j ∈ IdealMobiusDivisorSum.idealDivisors P,
        overlapPrefactor P j η Z r z (G j) * (idealRowHom u j)^2 *
          rowPolynomial (columns S P j)
            (overlapResidualCoefficient P j η a W Z r z (G j)) u := by
  rw [original_normalized_polynomial S hP (heckeIdealCharacter η u) a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [heckeIdealCharacter_apply,rowPolynomial,overlapPrefactor,
    overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

end SevenEighths.InverseInitialPoissonBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialConjugateEnergy
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss ConcreteTraceCRT
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialRayAttachment
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem overlapResidualCoefficient_conjugate (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal O) :
    overlapResidualCoefficient P j (conjugateIdealCharacter η)
        (fun I => star (a I)) (fun x => star (W x)) Z r z G c =
      star (overlapResidualCoefficient P j η a W Z r z G c) := by
  simp [overlapResidualCoefficient, star_mul, mul_comm, mul_left_comm, mul_assoc]

theorem star_conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    star (conjugatedResidual S P j η a W Z r z G u) =
      (Z^(-(r+z-2*G)/2) : ℝ) *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  unfold conjugatedResidual residualNormalizedPolynomial
  simp_rw [overlapResidualCoefficient_conjugate]
  simp [rowPolynomial, mul_comm]

theorem originalFixedPolynomial_eq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    originalFixedPolynomial S P j η a W Z r z u =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * (Z^(-G) : ℝ) *
        η j^2 * (idealRowHom u j)^2 * star (conjugatedResidual S P j η a W Z r z G u) := by
  rw [originalFixedPolynomial_eq S hP hj η a W hZ r z G,
    star_conjugatedResidual]
  unfold overlapPrefactor
  ring

theorem admissible_row_four_le_one (I : Ideal O) (hI : Admissible I) (u : O) :
    ‖idealRowHom u I‖^4 ≤ 1 := by
  have he := norm_idealRowHom_four_eq_two I hI u
  have hs : 0≤‖idealRowHom u I‖^2 := sq_nonneg _
  have ht : ‖idealRowHom u I‖^4=(‖idealRowHom u I‖^2)^2 := by ring
  rw [ht] at he ⊢
  nlinarith

theorem finite_weighted_triangle {α β : Type*} (J : Finset α) (R : Finset β)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ) :
    (∑ u ∈ R,w u * ‖∑ j ∈ J,F j u‖^2) ≤
      (∑ j ∈ J,Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2))^2 := by
  let v (j : α) : EuclideanSpace ℂ R :=
    WithLp.toLp 2 (fun u => (Real.sqrt (w u) : ℂ)*F j u)
  have hv (j : α) : ‖v j‖^2=∑ u ∈ R,w u*‖F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖F j u‖^2)
  have hsum : ‖∑ j ∈ J,v j‖^2=∑ u ∈ R,w u*‖∑ j ∈ J,F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,v,←Finset.mul_sum,norm_mul,mul_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖∑ j ∈ J,F j u‖^2)
  have hs := norm_sum_le J v
  have hn (j : α) : ‖v j‖=Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2) := by
    rw [←hv,Real.sqrt_sq (norm_nonneg _)]
  have hh := pow_le_pow_left₀ (norm_nonneg _) hs 2
  simpa only [hsum,hn] using hh

theorem originalTotalPolynomial_eq_sectors (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z : ℝ) (G : Ideal O → ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u =
      ∑ j∈idealDivisors P,originalFixedPolynomial S P j η a W Z r z u := by
  unfold originalTotalPolynomial
  rw [original_normalized_polynomial_hecke_rows S hP η a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  exact (originalFixedPolynomial_eq S hP ((mem_idealDivisors hP.ne_zero).mp hj)
    η a W hZ r z (G j) u).symm

end SevenEighths.InverseInitialConjugateEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPadding
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedPadding
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection ConcreteTraceCRT CanonicalQuadraticSieve ActualEisensteinCubic
local notation "O" => HeckeFamily.O

theorem radialMajorant_nonneg (x : ℝ) : 0≤(radialMajorant x).re :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.1 x

theorem radialMajorant_one (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : radialMajorant x=1 :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.2 x hx

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

end SevenEighths.DetectorDictionaryInverseMarkedPadding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedPolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialExcludedSource IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem prime_product_squarefree (S:Finset (Ideal O))(hS:∀P∈S,Prime P):
    Squarefree (∏P∈S,P) := by
  have hz:(∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hz).mpr
  have he:normalizedFactors (∏P∈S,P)=S.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=S.val) (fun P hP=>hS P hP)
  rw [he]
  exact S.nodup

end SevenEighths.InverseInitialExcludedPolynomial

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDivisors
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
open InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem tuple_product_squarefree (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Squarefree (∏i,P i) := by
  have hs:∀Q∈Finset.univ.image P,Prime Q := by
    intro Q hQ
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hQ
    exact hP i
  have he:(∏Q∈Finset.univ.image P,Q)=∏i,P i :=
    Finset.prod_image (fun i hi j hj h=>hinj h)
  rw [←he]
  exact InverseInitialExcludedPolynomial.prime_product_squarefree _ hs

omit [DecidableEq ι] in
theorem tuple_product_support (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (_hinj:Function.Injective P) : primeSupport (∏i,P i)=Finset.univ.image P := by
  have hn:(∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>(hP i).ne_zero)
  ext Q
  rw [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hn,Finset.mem_image]
  constructor
  · rintro ⟨hQ,hd⟩
    obtain ⟨i,hi,hd⟩:=(hQ.dvd_finsetProd_iff P).mp hd
    have he:Q=P i:=associated_iff_eq.mp (hQ.associated_of_dvd (hP i) hd)
    exact ⟨i,hi,he.symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hP i,Finset.dvd_prod_of_mem P hi⟩

omit [DecidableEq ι] in
theorem tuple_divisors_eq_subsets (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) :
    idealDivisors (∏i,P i)=Finset.univ.powerset.image (fun J:Finset ι=>∏i∈J,P i) := by
  have hs:=tuple_product_squarefree P hP hinj
  have hf:(idealDivisors (∏i,P i)).filter Squarefree=idealDivisors (∏i,P i) := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    exact hs.squarefree_of_dvd ((mem_idealDivisors hs.ne_zero).mp hJ)
  rw [←hf,squarefree_divisors_eq_image _ hs.ne_zero,tuple_product_support P hP hinj,
    Finset.powerset_image,Finset.image_image]
  congr 1
  funext J
  exact Finset.prod_image (fun i hi j hj h=>hinj h)

omit [Fintype ι] in
theorem tuple_subset_product_injective (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Function.Injective (fun J:Finset ι=>∏i∈J,P i) := by
  let:∀i,(P i).IsMaximal:=fun i=>(Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  exact FirstCauchyArithmetic.family_product_injective P hinj

theorem sum_tuple_divisors (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P)(f:Ideal O→ℂ) :
    (∑j∈idealDivisors (∏i,P i),f j)=∑J∈Finset.univ.powerset,f (∏i∈J,P i) := by
  rw [tuple_divisors_eq_subsets P hP hinj,Finset.sum_image
    (fun J hJ K hK he=>tuple_subset_product_injective P hP hinj he)]

theorem originalTotal_slot_subsets (S:Finset (Ideal O))
    (P:ι→Ideal O)(hP:∀i,Prime (P i))(hinj:Function.Injective P)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    originalTotalPolynomial S (∏i,P i) η a W Z r z u=
      ∑J∈Finset.univ.powerset,
        originalFixedPolynomial S (∏i,P i) (∏i∈J,P i) η a W Z r z u := by
  rw [originalTotalPolynomial_eq_sectors S (tuple_product_squarefree P hP hinj)
    η a W hZ r z (fun _=>0),sum_tuple_divisors P hP hinj]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceTuples
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem sum_tuple_split (L:ι→Finset (Ideal O))(J:Finset ι)(f:Tuple L→ℂ) :
    (∑q:Tuple L,f q)=∑x:Assigned L J,∑y:Remaining L J,f (joinTuple L J x y) := by
  rw [←(Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm.sum_comp]
  exact Fintype.sum_prod_type _

theorem tuple_injective (L:ι→Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Function.Injective (fun i=>(q i).val) := by
  intro i j he
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i) (Finset.mem_univ j) hij)
    (q i).property (by simpa only [he] using (q j).property)

theorem original_selected_subset_sum (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
  calc
    _ = ∑q:Tuple L,∑J∈Finset.univ.powerset,(∏i,coeff i (q i).val)*
        originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [originalTotal_slot_subsets S _ (fun i=>hprime i _ (q i).property)
        (tuple_injective L hdis q) η a W Z r z hZ u,Finset.mul_sum]
    _ = _ := Finset.sum_comm

theorem original_selected_grouped (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,∑y:Remaining L J,
      (∏i,coeff i (joinTuple L J x y i).val)*
        originalFixedPolynomial S (∏i,(joinTuple L J x y i).val)
          (∏i∈J,(joinTuple L J x y i).val) η a W Z r z u := by
  rw [original_selected_subset_sum S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  exact sum_tuple_split L J _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceProducts
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge InverseInitialOverlap
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] in
theorem joinTuple_assigned_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i∈J,(joinTuple L J x y i).val)=assignedIdeal L J x := by
  rw [←Finset.prod_coe_sort J (fun i=>(joinTuple L J x y i).val)]
  simp only [joinTuple_assigned,assignedIdeal]

theorem joinTuple_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i,(joinTuple L J x y i).val)=assignedIdeal L J x*remainingIdeal L J y := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>(joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert (preTransparency := .instances) he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

theorem joinTuple_coefficient_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(coeff:ι→Ideal O→ℂ) :
    (∏i,coeff i (joinTuple L J x y i).val)=
      (∏i:↥J,coeff i.val (x i).val)*(∏i:{i:ι // i∉J},coeff i.val (y i).val) := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>coeff i (joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert (preTransparency := .instances) he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem assignedIdeal_ne_zero (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J) : assignedIdeal L J x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi=>(hprime i.val _ (x i).property).ne_zero)

theorem original_selected_grouped_products (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*
      ∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
        originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
          (assignedIdeal L J x) η a W Z r z u := by
  rw [original_selected_grouped S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [joinTuple_coefficient_product,joinTuple_product,joinTuple_assigned_product]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceOverlap
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem assigned_remaining_squarefree (L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    Squarefree (assignedIdeal L J x*remainingIdeal L J y) := by
  rw [←joinTuple_product]
  exact tuple_product_squarefree _ (fun i=>hprime i _ (joinTuple L J x y i).property)
    (tuple_injective L hdis _)

theorem assigned_source_eq_remainingResidual (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    (∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
      originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
        (assignedIdeal L J x) η a W Z r z u)=
    (moebius (assignedIdeal L J x):ℂ)*(Z^(-G):ℝ)*η (assignedIdeal L J x)^2*
      (idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z G u) := by
  unfold remainingResidual
  simp only [star_sum,star_mul,star_star,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [originalFixedPolynomial_eq_conjugatedResidual S
    (assigned_remaining_squarefree L hprime hdis J x y) (dvd_mul_right _ _) η a W hZ r z G,
    InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]
  ring

theorem original_selected_overlap (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)
    (hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
      (Z^(-G J):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z (G J) u) := by
  rw [original_selected_grouped_products S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [assigned_source_eq_remainingResidual S L hprime hdis J x coeff η a W Z r z (G J) hZ u]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceRemaining
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic
open InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem remaining_injective (L:ι→Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) : Function.Injective (fun i=>(y i).val) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val) hij)
    (y i).property (by simpa only [he] using (y j).property)

theorem remaining_moebius (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) :
    (moebius (remainingIdeal L J y):ℂ)=(-1:ℂ)^Fintype.card {i:ι // i∉J} := by
  let:∀i:{i:ι // i∉J},((y i).val).IsMaximal:=fun i=>
    (Ideal.isPrime_of_prime (hprime i.val _ (y i).property)).isMaximal
      (hprime i.val _ (y i).property).ne_zero
  simpa only [remainingIdeal,Finset.card_univ] using prime_product_moebius
    (fun i=>(y i).val) (fun i=>hprime i.val _ (y i).property)
    (remaining_injective L hdis J y) Finset.univ

theorem remainingResidual_eq_polynomial (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingResidual S L J x coeff η (fun _=>1) W Z r z G u=
      (-1:ℂ)^Fintype.card {i:ι // i∉J}*
      remainingPolynomial S L J x coeff η W Z r z G u := by
  unfold remainingResidual remainingPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [remaining_moebius L hprime hdis]
  simp only [star_mul,star_prod,star_pow,star_neg,star_one,conjugatedResidual]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open UniqueFactorizationMonoid CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem assignedMass_nonneg (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ)(hZ:0<Z) : 0≤assignedMass L J x coeff Z G :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hZ.le _)

theorem assignedTerm_norm_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    ‖assignedTerm S L J x coeff η W Z r z G u‖≤
      assignedMass L J x coeff Z G*‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
  have hμ:‖(moebius (assignedIdeal L J x):ℂ)‖=1 := by simp [hj.2.1.moebius_eq]
  have hrow:‖idealRowHom u (assignedIdeal L J x)‖^2≤1 := by
    have hh:=admissible_row_four_le_one _ hj u
    nlinarith [sq_nonneg (‖idealRowHom u (assignedIdeal L J x)‖^2-1)]
  have hmass:=assignedMass_nonneg L J x coeff Z G hZ
  have he:‖η (assignedIdeal L J x)‖^2≤1:=pow_le_one₀ (norm_nonneg _) hη
  rw [assignedTerm,remainingResidual_eq_polynomial S L hprime hdis]
  simp only [norm_mul,norm_pow,norm_star,norm_neg,norm_one,one_pow,one_mul,
    hμ,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ.le (-G))]
  change assignedMass L J x coeff Z G*‖η (assignedIdeal L J x)‖^2*
    ‖idealRowHom u (assignedIdeal L J x)‖^2*
    ‖remainingPolynomial S L J x coeff η W Z r z G u‖≤_
  calc
    _≤assignedMass L J x coeff Z G*1*1*
      ‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
      gcongr
    _=_:=by ring

theorem assignedTerm_energy_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (assignedMass L J x coeff Z G)^2*
      ∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hh:=mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (assignedTerm_norm_le S L hprime hdis J x coeff η hj hη W Z r z G hZ u) 2)
    (hw u)
  convert (preTransparency := .instances) hh using 1 ; ring

theorem assigned_family_energy (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z G*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2))^2 := by
  refine (finite_weighted_triangle Finset.univ rows w hw
    (fun x u=>assignedTerm S L J x coeff η W Z r z G u)).trans ?_
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
  apply Finset.sum_le_sum
  intro x hx
  have hh:=Real.sqrt_le_sqrt (assignedTerm_energy_le S L hprime hdis J x coeff η
    (hj x) (hη x) W Z r z G hZ rows w hw)
  rwa [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (assignedMass_nonneg L J x coeff Z G hZ)] at hh

theorem original_energy_of_remaining (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)(hZ:0<Z)
    (rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u‖^2)≤
      (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff Z (G J))^2*E := by
  have heq (u:O) :
      (∑q:Tuple L,(∏i,coeff i (q i).val)*
        originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u)=
      ∑J∈Finset.univ.powerset,∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u :=
    original_selected_overlap S L hprime hdis coeff η (fun _=>1) W Z r z G hZ u
  simp_rw [heq]
  have hroot (J:Finset ι) :
      Real.sqrt (∑u∈rows,w u*‖∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
    have hm:0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J) :=
      Finset.sum_nonneg (fun x _=>assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hb:=assigned_family_energy S L hprime hdis J coeff η (hj J) (hη J)
      W Z r z (G J) hZ rows w hw
    have hc : (∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2))≤
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hres J x))
        (assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hn : 0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2) :=
      Finset.sum_nonneg (fun x _=>mul_nonneg (assignedMass_nonneg L J x coeff Z (G J) hZ) (Real.sqrt_nonneg _))
    have hh:=Real.sqrt_le_sqrt (hb.trans (pow_le_pow_left₀ hn hc 2))
    rwa [Real.sqrt_sq (mul_nonneg hm (Real.sqrt_nonneg E))] at hh
  refine (finite_weighted_triangle Finset.univ.powerset rows w hw
    (fun J u=>∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z (G J) u)).trans ?_
  calc
    _≤(∑J∈Finset.univ.powerset,
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
      exact Finset.sum_le_sum (fun J _=>hroot J)
    _=_:=by rw [←Finset.sum_mul,mul_pow,Real.sq_sqrt hE]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open InverseInitialExcludedPool
open InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceReindex
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialPoissonBridge InverseInitialConjugateEnergy InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem remaining_product_attach {A:Type*}[CommMonoid A]
    (J:Finset ι)(f:{i:ι // i∉J}→A) :
    (∏i,f i)=∏i∈(Finset.univ\J).attach,f ⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩ := by
  exact ((remainingIndexEquiv J).symm.prod_comp f).symm

theorem sum_remaining_original (L:ι→Finset (Ideal O))(J:Finset ι)
    (f:(∀i∈Finset.univ\J,Ideal O)→ℂ) :
    (∑q:Remaining L J,f (remainingPi L J q))=∑q∈(Finset.univ\J).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp hq i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he ⟨i,(Finset.mem_sdiff.mp hi).2⟩)
  · intro q hq
    refine ⟨remainingPi L J q,Finset.mem_pi.mpr (fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_original_pi (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ\J).pi L,(∏i∈(Finset.univ\J).attach,star (coeff i.val (q i.val i.property)))*
        residualNormalizedPolynomial S (assignedIdeal L J x*survivingProduct (Finset.univ\J) q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=>star (W v)) Z r z G u := by
  rw [←sum_remaining_original]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  unfold remainingIdeal survivingProduct remainingPi
  rw [remaining_product_attach J (fun i=>star (coeff i.val (q i).val)),
    remaining_product_attach J (fun i=>(q i).val)]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceArithmetic
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve InverseInitialCommonRatios InverseInitialExcludedPool
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem tuple_supported (L:ι→Finset (Ideal O))(hs:∀i,∀P∈L i,Supported P)(q:Tuple L) :
    Supported (∏i,(q i).val) := by
  have hh (T:Finset ι):Supported (∏i∈T,(q i).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi]
      exact (supported_mul_iff _ _).mpr ⟨hs i _ (q i).property,ih⟩
  exact hh Finset.univ

theorem tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Admissible (∏i,(q i).val) :=
  ⟨(tuple_supported L hs q).1,tuple_product_squarefree _ (fun i=>hp i _ (q i).property)
    (tuple_injective L hdis q),(tuple_supported L hs q).2⟩

theorem remainingIdeal_fromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    remainingIdeal L J (remainingFromPi L J t ht)=survivingProduct (Finset.univ\J) t := by
  unfold remainingIdeal
  rw [remaining_product_attach]
  rfl

theorem remaining_tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(t:∀i∈Finset.univ\J,Ideal O)
    (ht:t∈(Finset.univ\J).pi L) :
    Admissible (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_admissible L hp hs hdis _

theorem remaining_tuple_coprime (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    Pairwise (Function.onFun IsCoprime (fun i:↥(Finset.univ\J)=>t i.val i.property)) := by
  intro i j hij
  have hiP:=hp i.val _ (Finset.mem_pi.mp ht i.val i.property)
  have hjP:=hp j.val _ (Finset.mem_pi.mp ht j.val j.property)
  let:(t i.val i.property).IsMaximal:=(Ideal.isPrime_of_prime hiP).isMaximal hiP.ne_zero
  let:(t j.val j.property).IsMaximal:=(Ideal.isPrime_of_prime hjP).isMaximal hjP.ne_zero
  apply Ideal.isCoprime_of_isMaximal
  intro he
  dsimp only at he
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val)
    (fun hh=>hij (Subtype.ext hh))) (Finset.mem_pi.mp ht i.val i.property)
      (by rw [he];exact Finset.mem_pi.mp ht j.val j.property)

omit [DecidableEq ι] in
theorem tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(q:Tuple L) : outside E (∏i,(q i).val) := by
  intro P hP hd
  obtain ⟨i,hi,hdi⟩:=((hE P hP).dvd_finsetProd_iff (fun i=>(q i).val)).mp hd
  exact hout i _ (q i).property P hP hdi

theorem remaining_tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(J:Finset ι)(x:Assigned L J)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    outside E (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_outside L E hE hout _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceMass
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily DetectorDictionaryInverseAssignedCount
local notation "O"=>HeckeFamily.O

private theorem sum_tuple_real {ι:Type*}[Fintype ι](L:ι→Finset (Ideal O))
    (f:(ι→Ideal O)→ℝ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈assignedTuples L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,(mem_assignedTuples L q).mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,(mem_assignedTuples L _).mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] in
theorem assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (L:ι→Finset (Ideal O))(J:Finset ι)(hJ:J.card≤K)(ell:ι→ℝ)
    (hL:∀i∈J,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i∈J,∀P∈L i,‖coeff i P‖≤1) :
    (∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤assignedConstant K b := by
  have he:=assigned_sum_normalized_le K hb hU (by simpa using hJ)
    (fun i:↥J=>ell i) (fun i:↥J=>L i)
    (fun i P hP=>hL i i.property P hP)
    (fun i:↥J=>coeff i) (fun i P hP=>hc i i.property P hP)
  rw [←sum_tuple_real] at he
  simp only [assignedMass,assignedCoefficient,Finset.sum_coe_sort] at he ⊢
  convert (preTransparency := .instances) he using 1
  congr 1
  ext x
  simp

theorem all_assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(L:ι→Finset (Ideal O))(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1) :
    (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤
      (2:ℝ)^K*assignedConstant K b := by
  calc
    _≤∑J∈(Finset.univ:Finset ι).powerset,assignedConstant K b := by
      apply Finset.sum_le_sum
      intro J hJ
      exact assignedMass_sum_le K hb hU L J ((Finset.card_le_univ J).trans hK) ell
        (fun i _=>hL i) coeff (fun i _=>hc i)
    _=(2:ℝ)^Fintype.card ι*assignedConstant K b := by
      simp
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hK)
      (assignedConstant_pos K hb).le

theorem original_energy_with_assigned_count (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(r z:ℝ)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W U r z (∑i∈J,ell i) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      InverseInitialConjugateEnergy.originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W U r z u‖^2)≤
      ((2:ℝ)^K*assignedConstant K b)^2*E := by
  have hU0:0<U:=zero_lt_one.trans_le hU
  refine (original_energy_of_remaining S L hp hdis coeff η hj hη W U r z
    (fun J=>∑i∈J,ell i) hU0 rows w hw E hE hres).trans ?_
  apply mul_le_mul_of_nonneg_right _ hE
  apply pow_le_pow_left₀
    (Finset.sum_nonneg (fun J _=>Finset.sum_nonneg
      (fun x _=>assignedMass_nonneg L J x coeff U (∑i∈J,ell i) hU0)))
  exact all_assignedMass_sum_le K hb hU hK L ell hL coeff hc

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialMarkedAssignedGeometry
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialMarkedAssignedGeometry
open HeckeFamily ConcretePrimeRowBridge
open DetectorDictionaryInverseMarkedReference InverseInitialQuotientGeometry
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] in
 theorem assignedGenerator_mem (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):assignedGenerator L J x i=idealGenerator (x ⟨i,hi⟩).val:=by
  simp only [assignedGenerator,dif_pos hi]

omit [Fintype ι] in
 theorem assignedGenerator_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):Ideal.span {assignedGenerator L J x i}=(x ⟨i,hi⟩).val:=by
  rw [assignedGenerator_mem L J x i hi,span_idealGenerator]

omit [Fintype ι] in
 theorem assignedGenerator_ne_zero (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (hne:∀i∈J,∀P∈L i,P≠0)(i:ι)(hi:i∈J):assignedGenerator L J x i≠0:=by
  rw [assignedGenerator_mem L J x i hi]
  exact idealGenerator_ne_zero _ (hne i hi _ (x ⟨i,hi⟩).property)

omit [Fintype ι] in
 theorem assignedElement_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J):
    Ideal.span {assignedElement J (assignedGenerator L J x)}=assignedIdeal L J x:=by
  rw [assignedElement,FiniteGaussPhase.span_finset_prod,←Finset.prod_coe_sort]
  unfold assignedIdeal
  apply Finset.prod_congr rfl
  intro i hi
  exact assignedGenerator_span L J x i.val i.property

omit [Fintype ι] in
 theorem assignedGenerator_window_live (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(ell:ι→ℝ)(W:ι→ℝ→ℂ)
    (hW:∀i∈J,∀P∈L i,W i ((P.absNorm:ℝ)/U^(ell i))≠0):
    ∀i∈J,W i ((Ideal.absNorm (Ideal.span {assignedGenerator L J x i}):ℝ)/U^(ell i))≠0:=by
  intro i hi
  rw [assignedGenerator_span L J x i hi]
  exact hW i hi _ (x ⟨i,hi⟩).property

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_product (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ):
    (Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell)=
      ∏i:↥J,((x i).val.absNorm:ℝ)/U^(ell i.val):=by
  simp only [assignedIdeal,map_prod,Nat.cast_prod,Finset.prod_div_distrib,
    ←Real.rpow_sum_of_pos hU,Finset.sum_coe_sort,assignedCenter]

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_interval (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ)(K:ℕ)(hK:J.card≤K)
    (hL:∀i∈J,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2):
    ((Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell))∈Set.Icc (1:ℝ) ((2:ℝ)^K):=by
  rw [assigned_ratio_product L J x U hU ell]
  constructor
  · have hh:=Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun _i:↥J=>(1:ℝ)) (g:=fun i=>((x i).val.absNorm:ℝ)/U^(ell i.val))
      (fun _ _=>zero_le_one) (fun i _=>(hL i.val i.property _ (x i).property).1)
    simpa only [Finset.prod_const_one] using hh
  · calc
      _≤∏_i:↥J,(2:ℝ):=Finset.prod_le_prod
        (fun i _=>(zero_le_one.trans (hL i.val i.property _ (x i).property).1))
        (fun i _=>(hL i.val i.property _ (x i).property).2)
      _=(2:ℝ)^J.card:=by simp
      _≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hK

end SevenEighths.InverseInitialMarkedAssignedGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialMarkedReserve
namespace OAI

namespace SevenEighths.InverseInitialMarkedReserve

theorem exists_reserve (εm:ℝ)(hε:0<εm):
    ∃ρ gap η τ π eps loss:ℝ,
      0<ρ ∧ ρ≤1/4 ∧ ρ≤εm/4 ∧
      0<gap ∧ 2*gap≤ρ ∧
      0<η ∧ η≤1/7 ∧ η≤gap/50 ∧
      0<τ ∧ τ≤gap/50 ∧ 0<π ∧ 0<eps ∧ 0<loss ∧
      ρ+15*η+π+eps+loss≤εm:=by
  let ρ:=min (εm/4) (1/4)
  have hρ:0<ρ:=lt_min (by linarith) (by norm_num)
  have hρa:ρ≤εm/4:=min_le_left _ _
  have hρb:ρ≤1/4:=min_le_right _ _
  refine ⟨ρ,ρ/4,ρ/400,ρ/400,ρ/16,ρ/16,ρ/16,hρ,hρb,hρa,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem shifted_capacity (ρ gap η r r' ell G:ℝ)
    (hρ:0<ρ)(hρmax:ρ≤1/4)(hgap:2*gap≤ρ)
    (hη:0<η)(hηmax:η≤1/7)(hr:0≤ r)(hell:0≤ell)
    (_hG:0≤G)(hGmax:G≤ell)(hlo:r-η≤ r')(hhi:r'≤ r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3):
    0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤ r'+ell-2*G ∧
      r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧
      r'+ell+7*η≤2:=by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end SevenEighths.InverseInitialMarkedReserve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceSourceEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure
open InverseInitialMarkedAssignedGeometry DetectorDictionaryInverseRawConjugateGates
local notation "O"=>HeckeFamily.O

private theorem assigned_admissible {ι:Type}[Fintype ι][DecidableEq ι]
    (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J):Admissible (assignedIdeal L J x) := by
  apply tuple_admissible (fun i:↥J=>L i.val)
    (fun i=>hp i.val) (fun i=>hs i.val) _ x
  intro i hi j hj hij
  exact hdis (Finset.mem_univ _) (Finset.mem_univ _)
    (fun he=>hij (Subtype.ext he))

theorem original_source_energy
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (gap eps π eta τ loss:ℝ)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (heta:0<eta)(hetaone:eta≤1)(hetagap:eta≤gap/50)
    (hτ:0<τ)(hτgap:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∀q:ℕ,q≠0→∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U→(2:ℝ)^K≤U^eta→
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K→
    ∀(L:ι→Finset (Ideal O))(ell:ι→ℝ)(coeff:ι→Ideal O→ℂ),
      (∀i,0≤ell i)→(∀i,∀P∈L i,Prime P)→
      (∀i,∀P∈L i,Supported P)→
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)→
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,‖coeff i P‖≤1)→
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P)→
    ∀(primeW:ι→ℝ→ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀I,‖χ I‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ))→
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I→
        conjugateIdealCharacter χ I=0)→
    ∀m r:ℝ,0≤ m→m≤2→
      (∀J:Finset ι,-2≤ r+(∑i,ell i)-2*(∑i∈J,ell i))→
      r+2*(∑i,ell i)≤ m-2*gap→2*r+8*(∑i,ell i)≤3*m-2*gap→
      r+(∑i,ell i)+7*eta≤2→
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U^m)→∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U r (∑i,ell i) u‖^2)≤
      C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc ao bo := by
    intro x hx
    exact hsW (by simpa using hx)
  obtain ⟨degree,henergy⟩:=InverseInitialResidualUniformEnergy.original_residual_uniform_energy
    (fun x=>star (W x)) ao bo hao hab hsstar (Complex.conjCLE.contDiff.comp hW)
    DetectorDictionaryInverseMarkedPadding.radialMajorant
    DetectorDictionaryInverseMarkedPadding.radialMajorant_nonneg
    DetectorDictionaryInverseMarkedPadding.radialMajorant_one
    2 gap eps π eta τ loss (by norm_num) hgap heps hπ heta hetaone hetagap hτ hτgap hloss K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  let A:ℝ:=((2:ℝ)^K*DetectorDictionaryInverseAssignedCount.assignedConstant K 2)^2
  have hA:0<A:=sq_pos_of_pos (mul_pos (by positivity)
    (DetectorDictionaryInverseAssignedCount.assignedConstant_pos K (by norm_num)))
  refine ⟨A*C,U₀,mul_pos hA hC,hU₀,?_⟩
  intro U hU hpow ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero m r hm hmcap hD hfirst hsecond hparent rows hrows θ
  have hUone:1<U:=hU₀.trans_le hU
  have hUpos:0<U:=zero_lt_one.trans hUone
  have hscale (i:ι):0<U^(ell i):=Real.rpow_pos_of_pos hUpos _
  have hnorm (i:ι)(P:Ideal O)(hP:P∈L i):(P.absNorm:ℝ)≤2*U^(ell i):=
    (div_le_iff₀ (hscale i)).mp (hratio i P hP).2
  let E:ℝ:=C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2
  have hE:0≤E:=by dsimp [E];positivity
  have hres (J:Finset ι)(x:Assigned L J):
      (∑u∈rows,(1:ℝ)*‖remainingPolynomial (originalSource U r bo) L J x coeff χ
        (childLogTest W θ) U r (∑i,ell i) (∑i∈J,ell i) u‖^2)≤E := by
    have hJ:J.card≤K:=(Finset.card_le_univ J).trans hK
    have hH (i:ι):1≤2*U^(ell i) := by
      have hh:=Real.one_le_rpow hUone.le (hell i)
      linarith
    have hprod (T:Finset ι):
        (∏i∈T,2*U^(ell i))≤U^((∑i∈T,ell i)+eta) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hUpos,
        Real.rpow_add hUpos]
      rw [mul_comm (U^(∑i∈T,ell i))]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUpos.le _)
      exact (pow_le_pow_right₀ (by norm_num) ((Finset.card_le_univ T).trans hK)).trans hpow
    have hje:Admissible (assignedIdeal L J x):=assigned_admissible L hp hs hdis J x
    have hh:=henergy U hU Finset.univ J (Finset.subset_univ _) (by simpa using hK)
      L (fun i=>2*U^(ell i)) (fun i P=>star (coeff i P)) hdis
      (fun i _=>hH i) (fun i _=>hnorm i)
      (fun i _ P hP=>by simpa using hc i P hP)
      (assignedGenerator L J x) ell (fun _=>1) (fun _=>2) primeW
      (fun i _=>hell i)
      (assignedGenerator_ne_zero L J x (fun i _ P hP=>(hp i P hP).ne_zero))
      (fun i _=>hprimeW i) (assignedGenerator_window_live L J x U ell primeW (fun i _=>hlive i))
      (conjugateIdealCharacter χ)
      (fun u=>by simpa [elementCharacter,conjugateIdealCharacter] using hχ (Ideal.span {u}))
      hperiod hzero (r+(∑i,ell i)-2*(∑i∈J,ell i)) m r hm hmcap (hD J)
      (by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hJ).trans hpow)
      (by simpa [assignedCenter] using hprod (Finset.univ\J))
      rfl (by simpa [assignedCenter] using hfirst) (by simpa [assignedCenter] using hsecond)
      (by simpa [assignedCenter] using hparent) rows hrows (assignedIdeal L J x) hje
      (assignedElement_span L J x)
      (assigned_ratio_interval L J x U hUpos ell K hJ (fun i _=>hratio i))
      (fun i _=>hp i) (fun i _ P hP _=>hratio i P hP)
      (remaining_tuple_admissible L hp hs hdis J x)
      (remaining_tuple_coprime L hp hdis J)
      (remaining_tuple_outside L (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
        hout J x) (-θ)
    simpa only [one_mul,remainingPolynomial_original_pi,childLogTest_conjugate,
      assignedCenter,norm_neg,E] using hh
  have hb:=original_energy_with_assigned_count K (by norm_num : (1:ℝ)≤2) hUone.le hK
    (originalSource U r bo) L hp hdis ell (fun i P hP=>⟨(hp i P hP).ne_zero,hnorm i P hP⟩)
    coeff hc χ (assigned_admissible L hp hs hdis) (fun J x=>hχ _)
    (childLogTest W θ) r (∑i,ell i) rows (fun _=>1) (fun _=>zero_le_one) E hE hres
  simpa only [one_mul,E,A,mul_assoc] using hb

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePaddedEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure Filter
local notation "O"=>HeckeFamily.O

theorem padded_source_energy_oai
    (W:ℝ → ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃eta:ℝ,0<eta ∧ ∃degree:ℕ,∀q:ℕ,q≠0 → ∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K →
    ∀(L:ι → Finset (Ideal O))(ell:ι → ℝ)(coeff:ι → Ideal O → ℂ),
      (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
      (∀i,∀P∈L i,Supported P) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L) →
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,‖coeff i P‖≤1) →
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P) →
    ∀(primeW:ι → ℝ → ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0) →
    ∀χ:Ideal O →*ℂ,(∀I,‖χ I‖≤1) →
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ)) →
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I →
        conjugateIdealCharacter χ I=0) →
    ∀r rr:ℝ,0≤ r → r-eta≤ rr → rr≤ r →
      r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U rr bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U rr (∑i,ell i) u‖^2)≤
      C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨ρ,gap,eta,τ,π,eps,loss,hρ,hρmax,hρε,hgap,hgapρ,heta,hetamax,hetagap,
    hτ,hτgap,hπ,heps,hloss,hcost⟩:=InverseInitialMarkedReserve.exists_reserve εm hεm
  obtain ⟨degree,henergy⟩:=original_source_energy W ao bo hao hab hsW hW
    gap eps π eta τ loss hgap heps hπ heta (by linarith) hetagap hτ hτgap hloss K
  have hev:∀ᶠU:ℝ in atTop,(2:ℝ)^K≤U^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  obtain ⟨Uscale,hscale⟩:=eventually_atTop.mp hev
  refine ⟨eta,heta,degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  refine ⟨C,max U₀ Uscale,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero r rr hr hrlo hrhi hfirst hsecond rows hrows θ
  have hU0:U₀≤U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hs0:0≤∑i,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hG (J:Finset ι):0≤∑i∈J,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hGmax (J:Finset ι):(∑i∈J,ell i)≤∑i,ell i:=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)
  have hcap (J:Finset ι):
      0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤ rr+(∑i,ell i)-2*(∑i∈J,ell i) ∧
      rr+2*(∑i,ell i)≤1+ρ-2*gap ∧
      2*rr+8*(∑i,ell i)≤3*(1+ρ)-2*gap ∧ rr+(∑i,ell i)+7*eta≤2 :=
    InverseInitialMarkedReserve.shifted_capacity ρ gap eta r rr _ _ hρ hρmax hgapρ
      heta hetamax hr hs0 (hG J) (hGmax J) hrlo hrhi hfirst hsecond
  have hbase:=hcap ∅
  have hrows':∀u∈rows,‖eisEmbedding u‖^2≤U^(1+ρ) := by
    intro u hu
    refine (hrows u hu).trans ?_
    calc U=U^(1:ℝ):=(Real.rpow_one U).symm
         _≤U^(1+ρ):=Real.rpow_le_rpow_of_exponent_le hUone.le (by linarith)
  have hh:=henergy U hU0 (hscale U ((le_max_right _ _).trans hU)) hK L ell coeff hell hp hs
    hdis hratio hc hout primeW hprimeW hlive χ hχ hperiod hzero (1+ρ) rr
    hbase.1 hbase.2.1 (fun J=>(hcap J).2.2.1) hbase.2.2.2.1 hbase.2.2.2.2.1
    hbase.2.2.2.2.2 rows hrows' θ
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hUone.le
  linarith

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.DetectorDictionaryInverseMarkedReference.padded_source_energy_oai := @OAI.SevenEighths.DetectorDictionaryInverseMarkedReference.padded_source_energy_oai
