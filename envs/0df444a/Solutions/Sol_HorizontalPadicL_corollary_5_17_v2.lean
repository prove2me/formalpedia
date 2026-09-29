-- Prove2me | solution 1 for HorizontalPadicL.corollary_5_17_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T15:09:23.981987+00:00
-- url     : https://prove2.me/submissions/f8cb3e7c-2bdc-4387-94ef-d6e3d64eaa7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_KN_SeededInverseThetaSystemV2
import Definitions.Def_KN_InverseSeedConventionV2
import Theorems.Thm_HorizontalPadicL_algebraicSymbol_eq_signedModularSymbol_v3
import Theorems.Thm_HorizontalPadicL_eigenform_period_lattice_uniformly_integral_v2
import Theorems.Thm_HorizontalPadicL_fullSupportCriticalZeroSet_descends_inverseSeed_v3
import Theorems.Thm_HorizontalPadicL_fullSupport_atLevel_apply_eq_realized_v2
import Theorems.Thm_HorizontalPadicL_primitiveProductArithmetic_v2
import Theorems.Thm_HorizontalPadicL_realizedHorizontalCharacter_even_of_odd_prime_v2
import Theorems.Thm_HorizontalPadicL_seededEulerFactors_areUnits_v4
import Theorems.Thm_HorizontalPadicL_seededHorizontalCharacterRealization_exists_v4
import Theorems.Thm_HorizontalPadicL_seededHorizontalPadicLFunction_assemble_v4
import Theorems.Thm_HorizontalPadicL_seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2
import Theorems.Thm_HorizontalPadicL_unitNormRelationThetaSystem_to_normalizedMeasure_inverseSeed_v2
import Theorems.Thm_MTT_algebraicSymbol_horizontal_distribution
import Theorems.Thm_MTT_algebraicSymbol_horizontal_unitFiber_distribution
import Theorems.Thm_MTT_criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero
import Theorems.Thm_HorizontalPadicL_seededEigenform_padicPlace_exists_v2
import Theorems.Thm_HorizontalPadicL_newEigenform_residualRepresentation_exists_v2
import Theorems.Thm_HorizontalPadicL_seedCyclotomicGaloisCharacters_exist_v4
import Theorems.Thm_HorizontalPadicL_disjointRamification_seededFrobeniusClass_exists_v4
import Theorems.Thm_HorizontalPadicL_seededFrobeniusClass_positiveDensity_v2
import Theorems.Thm_HorizontalPadicL_seededFrobeniusClass_isOrderly_inverseSeed_v2
import Theorems.Thm_HorizontalPadicL_positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2
import Definitions.Def_KN_PrimePowerPropagationV2
import Mathlib.NumberTheory.MulChar.Duality
import Theorems.Thm_HorizontalPadicL_SeededHorizontalPadicLFunctionV4_primePower_propagation_v2
import Theorems.Thm_MTT_periods_exist
import Theorems.Thm_HorizontalPadicL_friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2

-- From Solutions/MatchingSignSymbol.lean
/-! The periodicity argument and period comparison adapt the accepted Prove2Me
proof by David Loeffler of `even_algebraicSymbol_sum_ne_zero_iff_modularSymbol_sum`
(submission `c7ded6e4-1fd6-48e2-aace-74f735a344a9`), archived in `submission/continuation/even-symbol-sum-source.lean`.
The reflection identity here retains the character value at -1, allowing
either parity when the modular-symbol sign matches the twisting character. -/

set_option autoImplicit false
noncomputable section BundleMatchingSignSymbol
open scoped BigOperators

namespace HorizontalPadicL

private theorem modularSymbol_add_modulus
    {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (j : ℕ) (a m : ℚ) (hm : m ≠ 0) :
    MTT.modularSymbol f j (a + m) m = MTT.modularSymbol f j a m := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f
    (show (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods by
      simp [MTT.GammaOne, CongruenceSubgroup.strictPeriods_Gamma1])
  unfold MTT.modularSymbol MTT.modularIntegral
  apply congrArg (fun z : ℂ => (2 * Real.pi : ℂ) * z)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have harg : (-(a + m) / m : ℂ) + Complex.I * t + 1 =
      (-a / m : ℂ) + Complex.I * t := by
    field_simp [hmC]
    ring
  have hf :
      f (UpperHalfPlane.ofComplex ((-(a + m) / m : ℚ) + Complex.I * t)) =
      f (UpperHalfPlane.ofComplex ((-a / m : ℚ) + Complex.I * t)) := by
    have h := hp ((-(a + m) / m : ℂ) + Complex.I * t)
    change f (UpperHalfPlane.ofComplex
      ((-(a + m) / m : ℂ) + Complex.I * t + 1)) =
      f (UpperHalfPlane.ofComplex ((-(a + m) / m : ℂ) + Complex.I * t)) at h
    rw [harg] at h
    push_cast at h ⊢
    exact h.symm
  dsimp only
  rw [hf]
  congr 1
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_smul,
    Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  congr 1
  linear_combination (m : ℂ) * harg

private theorem modularSymbol_neg_val
    {N k n : ℕ} [NeZero n]
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (j : ℕ) (a : ZMod n) :
    MTT.modularSymbol f j (-(a.val : ℚ)) n =
      MTT.modularSymbol f j (-a).val n := by
  by_cases ha : a = 0
  · subst a
    simp
  · let _ : NeZero a := ⟨ha⟩
    have hperiod := (modularSymbol_add_modulus f j (-(a.val : ℚ)) n
      (by exact_mod_cast NeZero.ne n)).symm
    rw [ZMod.val_neg_of_ne_zero]
    calc
      MTT.modularSymbol f j (-(a.val : ℚ)) n =
          MTT.modularSymbol f j (-(a.val : ℚ) + n) n := hperiod
      _ = MTT.modularSymbol f j (n - a.val : ℕ) n := by
        congr 2
        rw [Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt a))]
        ring

private theorem character_reflected_sum
    {n : ℕ} [NeZero n] (ι : MTT.Qbar →+* ℂ)
    (θ : DirichletCharacter MTT.Qbar n) (F : ZMod n → ℂ) :
    (∑ a : ZMod n, ι (θ a) * F (-a)) =
      ι (θ (-1)) * ∑ a : ZMod n, ι (θ a) * F a := by
  have hinv : ι (θ (-1)) * ι (θ (-1)) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  calc
    (∑ a : ZMod n, ι (θ a) * F (-a)) =
        ∑ a : ZMod n, ι (θ (-1)) * (ι (θ (-a)) * F (-a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show -a = (-1) * a by ring, map_mul, map_mul]
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    _ = ι (θ (-1)) * ∑ a : ZMod n, ι (θ (-a)) * F (-a) := by
      rw [Finset.mul_sum]
    _ = ι (θ (-1)) * ∑ a : ZMod n, ι (θ a) * F a := by
      congr 1
      exact Equiv.sum_comp (Equiv.neg (ZMod n)) (fun a ↦ ι (θ a) * F a)

/-- Every character has a modular-symbol sign matching its parity at any index. -/
theorem exists_matchingSign (η : DirichletCharacterWithLevel) (j : ℕ) :
    ∃ s : Bool, (MTT.sign s : MTT.Qbar) * (-1 : MTT.Qbar) ^ j = η.2 (-1) := by
  have hη : η.2 (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have hp : ((-1 : MTT.Qbar) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, neg_one_sq, one_pow]
  have ht : (η.2 (-1) * (-1 : MTT.Qbar) ^ j) ^ 2 = 1 := by
    rw [mul_pow, hη, hp, one_mul]
  obtain ⟨s, hs⟩ : ∃ s : Bool,
      (MTT.sign s : MTT.Qbar) = η.2 (-1) * (-1 : MTT.Qbar) ^ j := by
    rcases sq_eq_one_iff.mp ht with h | h
    · exact ⟨true, by simpa [MTT.sign] using h.symm⟩
    · exact ⟨false, by simpa [MTT.sign] using h.symm⟩
  refine ⟨s, ?_⟩
  rw [hs, mul_assoc, ← pow_two, hp, mul_one]

/-- Passing to a primitive product preserves parity multiplication. -/
theorem primitiveProductV2_apply_neg_one (η ψ : DirichletCharacterWithLevel) :
    (primitiveProductV2 η ψ).2 (-1) = η.2 (-1) * ψ.2 (-1) := by
  have : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  have : NeZero ψ.1.1 := ⟨Nat.ne_of_gt ψ.1.2⟩
  have : NeZero (Nat.lcm η.1.1 ψ.1.1) :=
    ⟨Nat.lcm_ne_zero (Nat.ne_of_gt η.1.2) (Nat.ne_of_gt ψ.1.2)⟩
  have hcop : IsCoprime (-1 : ℤ) (Nat.lcm η.1.1 ψ.1.1 : ℤ) :=
    isCoprime_one_left.neg_left
  have hprimitive :=
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime (η.2.mul ψ.2) hcop
  simp only [Int.cast_neg, Int.cast_one] at hprimitive
  change (η.2.mul ψ.2).primitiveCharacter (-1) = _
  rw [hprimitive, DirichletCharacter.mul, MulChar.mul_apply]
  have hleft := DirichletCharacter.changeLevel_eq_cast_of_dvd' η.2
    (Nat.dvd_lcm_left η.1.1 ψ.1.1) hcop
  have hright := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ.2
    (Nat.dvd_lcm_right η.1.1 ψ.1.1) hcop
  simp only [Int.cast_neg, Int.cast_one] at hleft hright
  rw [hleft, hright]

/-- An even auxiliary character leaves the seed parity unchanged. -/
theorem primitiveProductV2_apply_neg_one_of_even (η ψ : DirichletCharacterWithLevel)
    (hψeven : ψ.2 (-1) = 1) :
    (primitiveProductV2 η ψ).2 (-1) = η.2 (-1) := by
  rw [primitiveProductV2_apply_neg_one, hψeven, mul_one]

theorem matchingSign_algebraicSymbol_sum_ne_zero_iff_modularSymbol_sum
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (hk : 2 ≤ k) (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form)
    (θ : DirichletCharacterWithLevel)
    (s : Bool)
    (hs : (MTT.sign s : MTT.Qbar) * (-1 : MTT.Qbar) ^ (k / 2 - 1) = θ.2 (-1))
    (hcomparison : ∀ s j a m, j ≤ k - 2 → m ≠ 0 →
      ι (MTT.algebraicSymbol P s j a m) * P.omega s =
        signedModularSymbol f.form s j a m) :
    letI : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
    ((∑ a : ZMod θ.1.1,
        θ.2 a * MTT.algebraicSymbol P s (k / 2 - 1) a.val θ.1.1) ≠ 0 ↔
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form
          (k / 2 - 1) a.val θ.1.1) ≠ 0) := by
  let _ : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
  let j := k / 2 - 1
  have hj : j ≤ k - 2 := by omega
  have hn : (θ.1.1 : ℚ) ≠ 0 := by exact_mod_cast θ.1.2.ne'
  let A : MTT.Qbar := ∑ a : ZMod θ.1.1,
    θ.2 a * MTT.algebraicSymbol P s j a.val θ.1.1
  let S : ℂ := ∑ a : ZMod θ.1.1,
    ι (θ.2 a) * MTT.modularSymbol f.form j a.val θ.1.1
  let Ssigned : ℂ := ∑ a : ZMod θ.1.1,
    ι (θ.2 a) * signedModularSymbol f.form s j a.val θ.1.1
  have hperiod : ι A * P.omega s = Ssigned := by
    dsimp only [A, Ssigned]
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_mul]
    rw [mul_assoc, hcomparison s j a.val θ.1.1 hj hn]
  have hsC : (MTT.sign s : ℂ) * (-1 : ℂ) ^ j = ι (θ.2 (-1)) := by
    simpa only [map_mul, map_intCast, map_pow, map_neg, map_one, j] using
      congrArg ι hs
  have hsign : ((MTT.sign s : ℂ) * (-1 : ℂ) ^ j) * ι (θ.2 (-1)) = 1 := by
    rw [hsC, ← map_mul, ← map_mul]
    simp
  have hreflect :
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form j (-a).val θ.1.1) = ι (θ.2 (-1)) * S := by
    simpa only [S] using character_reflected_sum ι θ.2
      (fun a => MTT.modularSymbol f.form j a.val θ.1.1)
  have hnegative :
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form j (-(a.val : ℚ)) θ.1.1) = ι (θ.2 (-1)) * S := by
    calc
      _ = ∑ a : ZMod θ.1.1,
          ι (θ.2 a) * MTT.modularSymbol f.form j (-a).val θ.1.1 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [modularSymbol_neg_val]
      _ = ι (θ.2 (-1)) * S := hreflect
  have hsigned : Ssigned = S := by
    let T : ℂ := ∑ a : ZMod θ.1.1,
      ι (θ.2 a) * MTT.modularSymbol f.form j (-(a.val : ℚ)) θ.1.1
    have hexpand : Ssigned = (S +
        ((MTT.sign s : ℂ) * (-1 : ℂ) ^ j) * T) / 2 := by
      dsimp only [Ssigned, S, T]
      calc
        (∑ a : ZMod θ.1.1,
          ι (θ.2 a) * signedModularSymbol f.form s j a.val θ.1.1) =
            ∑ a : ZMod θ.1.1,
              (ι (θ.2 a) * MTT.modularSymbol f.form j a.val θ.1.1 +
                ((MTT.sign s : ℂ) * (-1 : ℂ) ^ j) *
                  (ι (θ.2 a) * MTT.modularSymbol f.form j
                    (-(a.val : ℚ)) θ.1.1)) / 2 := by
          apply Finset.sum_congr rfl
          intro a _
          unfold signedModularSymbol
          ring
        _ = (∑ a : ZMod θ.1.1,
              (ι (θ.2 a) * MTT.modularSymbol f.form j a.val θ.1.1 +
                ((MTT.sign s : ℂ) * (-1 : ℂ) ^ j) *
                  (ι (θ.2 a) * MTT.modularSymbol f.form j
                    (-(a.val : ℚ)) θ.1.1))) / 2 := by
          rw [Finset.sum_div]
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hexpand, show T = ι (θ.2 (-1)) * S by exact hnegative,
      ← mul_assoc, hsign, one_mul]
    ring
  change A ≠ 0 ↔ S ≠ 0
  rw [← hsigned, ← hperiod]
  constructor
  · intro hA
    exact mul_ne_zero ((map_ne_zero_iff ι ι.injective).2 hA) (P.omega_ne s)
  · intro hprod hA
    apply hprod
    rw [hA, map_zero, zero_mul]

end HorizontalPadicL

end BundleMatchingSignSymbol

-- From Solutions/SeededThetaAnyParity.lean
/-!
The seeded theta construction with the modular-symbol sign chosen to match the
seed character. This extends the existing construction to both seed parities.

The underlying Prove2Me proofs are adapted from cbirkbeck's theta existence
submission `3d5e5630`, davidloeffler's projection submission `0b7ddfe9` and norm
relations submission `f1d595ec`, and frknbls's evaluation submission `69fe8a06`.
The zero-set descent and final assembly also use davidloeffler's platform proofs.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section BundleSeededThetaAnyParity
open scoped BigOperators

namespace HorizontalPadicL

def SeededFiniteThetaDataV3.IsInverseSeedThetaSystemForSign
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (P : MTT.Periods k ι f.form)
    (scale : IntegralPeriodScale f ιp P) (s : Bool) : Prop :=
  letI : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  (∀ (A : Finset ℕ) (g : HorizontalFiniteGroup p L.exponent A),
    let M := L.supportModulus A
    let q := η.2.conductor * M
    letI : NeZero q := ⟨mul_ne_zero η.2.conductor_ne_zero
      (Nat.ne_of_gt (L.supportModulus_pos A))⟩
    (((Θ.theta A).coeff g : Θ.coefficientRing) : ℂ_[p]) =
      ∑ u : (ZMod q)ˣ,
        if Θ.characters.projections.supportProjection A
            (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) u) = g then
          ιp (scale.scale * η.2 u.val.val *
            MTT.algebraicSymbol P s (k / 2 - 1) u.val.val q /
              (M : MTT.Qbar) ^ (k / 2 - 1))
        else 0) ∧
  ∀ (A : Finset ℕ) (n : ℕ) (hn : n ∉ A),
    MonoidAlgebra.mapRingHom
        (HorizontalFiniteGroup p L.exponent A) Θ.coefficientRing.subtype
        (Θ.eulerFactor A n) =
      inverseSeedEulerFactorCp Θ.characters A n hn
end HorizontalPadicL


open scoped BigOperators

namespace HorizontalPadicL.AnyParityExists

open HorizontalPadicL

section Norms

variable {p : ℕ} [Fact p.Prime]

lemma mem_integers_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm]
  show (PadicComplex.valued p).v x ≤ 1 ↔ _
  rw [Valuation.norm_def]
  simp [PadicComplex.RankOne.hom_eq_embedding]

lemma norm_natCast_eq_one {n : ℕ} (h : Nat.Coprime p n) : ‖(n : ℂ_[p])‖ = 1 := by
  have := norm_algebraMap' ℂ_[p] (n : ℚ_[p])
  rw [map_natCast] at this
  rw [this]
  exact Padic.norm_natCast_eq_one_iff.mpr h

lemma norm_natCast_lt_one {n : ℕ} (h : p ∣ n) : ‖(n : ℂ_[p])‖ < 1 := by
  have := norm_algebraMap' ℂ_[p] (n : ℚ_[p])
  rw [map_natCast] at this
  rw [this]
  exact Padic.norm_natCast_lt_one_iff.mpr h

lemma norm_eq_one_of_pow_eq_one' {x : ℂ_[p]} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) :
    ‖x‖ = 1 := by
  have : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp this

lemma norm_char_unit (ιp : MTT.Qbar →+* ℂ_[p]) {n : ℕ} [NeZero n]
    (χ : DirichletCharacter MTT.Qbar n) (u : (ZMod n)ˣ) : ‖ιp (χ u)‖ = 1 := by
  apply norm_eq_one_of_pow_eq_one' (n := Fintype.card (ZMod n)ˣ) Fintype.card_ne_zero
  rw [← map_pow, ← MulChar.pow_apply_coe, MulChar.pow_card_eq_one, MulChar.one_apply_coe,
    map_one]

lemma norm_char_le (ιp : MTT.Qbar →+* ℂ_[p]) {n : ℕ} [NeZero n]
    (χ : DirichletCharacter MTT.Qbar n) (x : ZMod n) : ‖ιp (χ x)‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [norm_char_unit]
  · rw [MulChar.map_nonunit χ hx, map_zero, norm_zero]
    exact zero_le_one

lemma norm_char_natCast_eq_one (ιp : MTT.Qbar →+* ℂ_[p]) {n : ℕ} [NeZero n]
    (χ : DirichletCharacter MTT.Qbar n) {ℓ : ℕ} (h : Nat.Coprime ℓ n) :
    ‖ιp (χ ℓ)‖ = 1 := by
  have hu : IsUnit (ℓ : ZMod n) := (ZMod.isUnit_iff_coprime ℓ n).mpr h
  obtain ⟨u, hu⟩ := hu
  rw [← hu]
  exact norm_char_unit ιp χ u

end Norms

section Construction

variable {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
  {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
  {η : DirichletCharacterWithLevel}

/-- The integral coefficient ring of the constructed theta system. -/
abbrev O (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := (𝓞_ℂ_[p]).toSubring

/-- The inverse-seed modular-symbol summand attached to a unit `u` modulo `q`. -/
def summand (P : MTT.Periods k ι f.form) (scale : IntegralPeriodScale f ιp P) (s : Bool)
    (M q : ℕ) (u : (ZMod q)ˣ) : ℂ_[p] :=
  ιp (scale.scale * η.2 u.val.val *
    MTT.algebraicSymbol P s (k / 2 - 1) u.val.val q / (M : MTT.Qbar) ^ (k / 2 - 1))

omit [Fact p.Prime] in
lemma scale_mul_algebraicSymbol (P : MTT.Periods k ι f.form) (sc : MTT.Qbar) (s : Bool)
    (j : ℕ) (a m : ℚ) :
    sc * MTT.algebraicSymbol P s j a m = ∑ t ∈ Finset.range (j + 1),
      (j.choose t : MTT.Qbar) * (m : MTT.Qbar) ^ t * (a : MTT.Qbar) ^ (j - t) *
        (sc * P.value s t (-a / m)) := by
  rw [MTT.algebraicSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

lemma summand_mem (hk : 2 ≤ k) (P : MTT.Periods k ι f.form)
    (scale : IntegralPeriodScale f ιp P) (s : Bool) {M q : ℕ} (hM : Nat.Coprime p M)
    (u : (ZMod q)ˣ) : summand (η := η) P scale s M q u ∈ 𝓞_ℂ_[p] := by
  have hη : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  have hsym : ιp (scale.scale * MTT.algebraicSymbol P s (k / 2 - 1)
      ((u.val.val : ℕ) : ℚ) ((q : ℕ) : ℚ)) ∈ 𝓞_ℂ_[p] := by
    rw [scale_mul_algebraicSymbol, map_sum]
    refine Subring.sum_mem (O p) fun t ht => ?_
    have ht' : t ≤ k - 2 := by
      have := Finset.mem_range.mp ht
      omega
    have hint := scale.integral_value s t (-((u.val.val : ℕ) : ℚ) / ((q : ℕ) : ℚ)) ht'
    simp only [map_mul, map_pow, Rat.cast_natCast, map_natCast]
    exact Subring.mul_mem (O p) (Subring.mul_mem (O p) (Subring.mul_mem (O p)
      (natCast_mem _ _) (Subring.pow_mem _ (natCast_mem _ _) _))
      (Subring.pow_mem _ (natCast_mem _ _) _)) (by rw [map_mul] at hint; exact hint)
  rw [mem_integers_iff] at hsym ⊢
  have hMnorm : ‖ιp (M : MTT.Qbar)‖ = 1 := by
    rw [map_natCast]; exact norm_natCast_eq_one hM
  have hrw : summand (η := η) P scale s M q u =
      ιp (η.2 u.val.val) * ιp (scale.scale * MTT.algebraicSymbol P s (k / 2 - 1)
        ((u.val.val : ℕ) : ℚ) ((q : ℕ) : ℚ)) / ιp (M : MTT.Qbar) ^ (k / 2 - 1) := by
    rw [summand, map_div₀, map_pow, map_mul, map_mul, map_mul]
    ring
  rw [hrw, norm_div, norm_mul, norm_pow, hMnorm, one_pow, div_one]
  have := norm_char_le ιp η.2 (u.val.val : ZMod η.1.1)
  nlinarith [norm_nonneg (ιp (η.2 u.val.val))]

end Construction

section Euler

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric perturbation: dividing the linear term by a principal unit does not change
the norm of an orderly Euler expression. -/
lemma norm_augmentation_eq {e A E L : ℂ_[p]} (he : ‖e‖ = 1) (hA : ‖A‖ ≤ 1) (hL : ‖L‖ = 1)
    (hL1 : ‖L - 1‖ < 1) (hx : ‖e * A - e ^ 2 - E‖ = 1) :
    ‖A / L - e - E * e⁻¹‖ = ‖e * A - e ^ 2 - E‖ := by
  have he0 : e ≠ 0 := by intro h; rw [h, norm_zero] at he; exact zero_ne_one he
  have hL0 : L ≠ 0 := by intro h; rw [h, norm_zero] at hL; exact zero_ne_one hL
  have hsplit : e * (A / L - e - E * e⁻¹) =
      (e * A - e ^ 2 - E) + e * A * (1 - L) / L := by
    field_simp
    ring
  have hsmall : ‖e * A * (1 - L) / L‖ < 1 := by
    rw [norm_div, norm_mul, norm_mul, he, hL, one_mul, div_one, norm_sub_rev]
    calc ‖A‖ * ‖L - 1‖ ≤ 1 * ‖L - 1‖ :=
          mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hL1
  have hsum : ‖(e * A - e ^ 2 - E) + e * A * (1 - L) / L‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hx]; exact hsmall.ne'), hx]
    exact max_eq_left hsmall.le
  rw [hx]
  have := congrArg norm hsplit
  rw [norm_mul, he, one_mul, hsum] at this
  exact this

end Euler

section Main

variable {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
  {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
  {η : DirichletCharacterWithLevel}

/-- Local norm facts at an auxiliary orderly prime. -/
lemma primeAt_norms (hN : 0 < N) (hηprim : η.2.IsPrimitive)
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) (n : ℕ) :
    Nat.Coprime p (L.primeAt n) ∧ p ∣ L.primeAt n - 1 ∧
      ‖ιp (η.2 (L.primeAt n))‖ = 1 ∧ ‖ιp (f.epsilon (L.primeAt n))‖ = 1 ∧
      ‖ιp (f.coeff (L.primeAt n))‖ ≤ 1 := by
  obtain ⟨hprime, hmod, hcop, hunit⟩ := L.primeAt_orderly n
  have hp := (Fact.out : p.Prime)
  have hℓ1 : 1 ≤ L.primeAt n := hprime.one_lt.le
  have hdvd : p ∣ L.primeAt n - 1 :=
    Nat.dvd_trans (dvd_pow_self p (Nat.pos_iff_ne_zero.mp L.orderExponent_pos))
      ((Nat.modEq_iff_dvd' hℓ1).mp hmod.symm)
  have hcopℓ : Nat.Coprime p (L.primeAt n) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hp.one_lt.ne' ?_
    have := Nat.dvd_sub h hdvd
    rw [Nat.sub_sub_self hℓ1] at this
    exact Nat.dvd_one.mp this
  have hNZ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hηZ : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  have hηlev : η.2.conductor = η.1.1 := hηprim
  have he : ‖ιp (η.2 (L.primeAt n))‖ = 1 := by
    refine norm_char_natCast_eq_one ιp η.2 ?_
    rw [← hηlev]
    exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hcop
  have hε : ‖ιp (f.epsilon (L.primeAt n))‖ = 1 :=
    norm_char_natCast_eq_one ιp f.epsilon
      (Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hcop)
  refine ⟨hcopℓ, hdvd, he, hε, ?_⟩
  set x := ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) - (η.2 (L.primeAt n)) ^ 2 -
    f.epsilon (L.primeAt n)) with hx
  have hsum : ιp (η.2 (L.primeAt n)) * ιp (f.coeff (L.primeAt n)) =
      x + ιp (η.2 (L.primeAt n)) ^ 2 + ιp (f.epsilon (L.primeAt n)) := by
    rw [hx]; simp only [map_sub, map_mul, map_pow]; ring
  have hle : ‖ιp (η.2 (L.primeAt n)) * ιp (f.coeff (L.primeAt n))‖ ≤ 1 := by
    rw [hsum]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
      · rw [hx, hunit]
      · rw [norm_pow, he, one_pow]
    · rw [hε]
  rwa [norm_mul, he, one_mul] at hle

end Main

end HorizontalPadicL.AnyParityExists

open HorizontalPadicL HorizontalPadicL.AnyParityExists in
theorem HorizontalPadicL.seededInverseThetaSystem_exists_forSign
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (P : MTT.Periods k ι f.form) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (ιp : MTT.Qbar →+* ℂ_[p]) (hpodd : p ≠ 2)
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (characters : SeededHorizontalCharacterRealizationV3 L)
    (scale : IntegralPeriodScale f ιp P) (s : Bool) :
    ∃ Θ : SeededFiniteThetaDataV3 L,
      Θ.characters = characters ∧ Θ.IsInverseSeedThetaSystemForSign P scale s := by
  have hηZ : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  have key := primeAt_norms hN hηprim L
  have hMcop : ∀ A : Finset ℕ, Nat.Coprime p (L.supportModulus A) := fun A =>
    Nat.Coprime.prod_right fun n _ => (key n).1
  -- Integrality of the three Euler coefficients at a new prime.
  have hj : ∀ n, ‖((L.primeAt n : ℂ_[p]) ^ (k / 2 - 1))‖ = 1 := fun n => by
    rw [norm_pow, norm_natCast_eq_one (key n).1, one_pow]
  have m1 : ∀ n, ιp (f.coeff (L.primeAt n)) / (L.primeAt n : ℂ_[p]) ^ (k / 2 - 1) ∈ O p :=
    fun n => by
      show _ ∈ 𝓞_ℂ_[p]
      rw [mem_integers_iff, norm_div, hj, div_one]; exact (key n).2.2.2.2
  have m2 : ∀ n, ιp (η.2 (L.primeAt n)) ∈ O p := fun n => by
    show _ ∈ 𝓞_ℂ_[p]
    rw [mem_integers_iff, (key n).2.2.1]
  have m3 : ∀ n, ιp (f.epsilon (L.primeAt n) * (η.2 (L.primeAt n))⁻¹) ∈ O p := fun n => by
    show _ ∈ 𝓞_ℂ_[p]
    rw [mem_integers_iff, map_mul, map_inv₀, norm_mul, norm_inv, (key n).2.2.1,
      (key n).2.2.2.1]
    norm_num
  have m4 : ∀ n, ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) -
      (η.2 (L.primeAt n)) ^ 2 - f.epsilon (L.primeAt n)) ∈ O p := fun n => by
    show _ ∈ 𝓞_ℂ_[p]
    rw [mem_integers_iff, (L.primeAt_orderly n).2.2.2]
  let E : ∀ (A : Finset ℕ) (n : ℕ), HorizontalGroupAlgebra (O p) p L.exponent A :=
    fun A n =>
      if hn : n ∉ A then
        MonoidAlgebra.single 1 ⟨_, m1 n⟩ -
          MonoidAlgebra.single (characters.horizontalPrimeElement A n hn) ⟨_, m2 n⟩ -
          MonoidAlgebra.single (characters.horizontalPrimeElement A n hn)⁻¹ ⟨_, m3 n⟩
      else MonoidAlgebra.single 1 ⟨_, m4 n⟩
  have hE_aug : ∀ (A : Finset ℕ) (n : ℕ),
      ‖((horizontalAugmentation (E A n) : O p) : ℂ_[p])‖ =
        ‖ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) -
          (η.2 (L.primeAt n)) ^ 2 - f.epsilon (L.primeAt n))‖ := by
    intro A n
    by_cases hn : n ∉ A
    · simp only [E, dif_pos hn, horizontalAugmentation, map_sub, MonoidAlgebra.lift_single,
        MonoidHom.one_apply, smul_eq_mul, mul_one]
      obtain ⟨-, hdvd, he, hε, hA⟩ := key n
      have hL1 : ‖(L.primeAt n : ℂ_[p]) ^ (k / 2 - 1) - 1‖ < 1 := by
        have hpow : 1 ≤ L.primeAt n ^ (k / 2 - 1) :=
          Nat.one_le_pow _ _ (L.primeAt_prime n).pos
        have hd : p ∣ L.primeAt n ^ (k / 2 - 1) - 1 := by
          have := Nat.sub_dvd_pow_sub_pow (L.primeAt n) 1 (k / 2 - 1)
          rw [one_pow] at this
          exact Nat.dvd_trans hdvd this
        have := norm_natCast_lt_one hd
        rwa [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one] at this
      have hx := (L.primeAt_orderly n).2.2.2
      simp only [map_sub, map_mul, map_pow] at hx ⊢
      have := norm_augmentation_eq he hA (hj n) hL1 hx
      rw [← map_inv₀] at this
      exact this
    · simp only [E, dif_neg hn, horizontalAugmentation, MonoidAlgebra.lift_single,
        MonoidHom.one_apply, smul_eq_mul, mul_one]
  refine ⟨{ coefficientRing := O p
            coefficientRing_eq := rfl
            coefficient_integral := fun x => x.2
            characters := characters
            theta := fun A =>
              letI : NeZero (η.2.conductor * L.supportModulus A) :=
                ⟨mul_ne_zero η.2.conductor_ne_zero (Nat.ne_of_gt (L.supportModulus_pos A))⟩
              ∑ u : (ZMod (η.2.conductor * L.supportModulus A))ˣ,
                MonoidAlgebra.single
                  (characters.projections.supportProjection A
                    (ZMod.unitsMap (Nat.dvd_mul_left (L.supportModulus A) η.2.conductor) u))
                  (⟨summand (η := η) P scale s (L.supportModulus A)
                      (η.2.conductor * L.supportModulus A) u,
                    summand_mem hk P scale s (hMcop A) u⟩ : O p)
            eulerFactor := E
            eulerFactor_augmentation_norm := hE_aug }, rfl, ?_, ?_⟩
  · intro A g
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
    push_cast [apply_ite]
    simp only [summand, Nat.cast_mul]
  · intro A n hn
    simp only [E, dif_pos hn, map_sub, MonoidAlgebra.mapRingHom_single, inverseSeedEulerFactorCp, Subring.subtype_apply]


open scoped BigOperators

namespace HorizontalPadicL.AnyParityProjection

private theorem supportModulus_insert
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (A : Finset ℕ) (n : ℕ) (hn : n ∉ A) :
    L.supportModulus (insert n A) = L.primeAt n * L.supportModulus A := by
  simp [SeededHorizontalPrimeDataV3.supportModulus, hn]

private theorem supportProjection_restrict
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel} {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalProjectionSystemV3 L)
    {A C : Finset ℕ} (hCA : C ⊆ A)
    (h : L.supportModulus C ∣ L.supportModulus A)
    (u : (ZMod (L.supportModulus A))ˣ) :
    horizontalRestrictionHom hCA (R.supportProjection A u) =
      R.supportProjection C (ZMod.unitsMap h u) := by
  ext i
  change R.localProjection i.1 (ZMod.unitsMap _ u) =
    R.localProjection i.1 (ZMod.unitsMap _ (ZMod.unitsMap h u))
  congr 1
  exact (DFunLike.congr_fun (ZMod.unitsMap_comp
    (Finset.dvd_prod_of_mem L.primeAt i.2) h) u).symm

private theorem horizontalRestrictionHom_surjective
    {p : ℕ} {m : ℕ → ℕ} {A C : Finset ℕ} (hCA : C ⊆ A) :
    Function.Surjective (horizontalRestrictionHom (p := p) (m := m) hCA) := by
  intro x
  let y : HorizontalFiniteGroup p m A := fun i =>
    if hi : i.1 ∈ C then x ⟨i.1, hi⟩ else 1
  refine ⟨y, ?_⟩
  ext i
  change (if hi : i.1 ∈ C then x ⟨i.1, hi⟩ else 1) = x i
  rw [dif_pos i.2]

private theorem mapDomain_coefficient_of_formula
    {R S H K U : Type*} [AddCommMonoid R] [AddCommMonoid S]
    [Fintype H] [Fintype U] [DecidableEq H] [DecidableEq K]
    (φ : R →+ S) (x : H →₀ R) (π : U → H) (r : H → K) (g : K)
    (w : U → S) (hx : ∀ h, φ (x h) = ∑ u, if π u = h then w u else 0) :
    φ ((Finsupp.mapDomain r x) g) = ∑ u, if r (π u) = g then w u else 0 := by
  classical
  have hcoeff : (Finsupp.mapDomain r x) g =
      ∑ a : H, if r a = g then x a else 0 := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    simpa only [Finsupp.single_apply] using
      x.sum_fintype (fun a b => if r a = g then b else 0) (by simp)
  rw [hcoeff, map_sum]
  calc
    ∑ a : H, φ (if r a = g then x a else 0) =
        ∑ a : H, (if r a = g then φ (x a) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hag : r a = g <;> simp [hag]
    _ =
        ∑ a : H, if r a = g then
          (∑ u, if π u = a then w u else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases hag : r a = g <;> simp [hag, hx]
    _ = ∑ a : H, ∑ u : U,
          if π u = a ∧ r a = g then w u else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases hag : r a = g
            · simp only [hag, and_true, if_true]
            · simp [hag]
    _ = ∑ u : U, ∑ a : H,
          if π u = a ∧ r a = g then w u else 0 := Finset.sum_comm
    _ = ∑ u : U, if r (π u) = g then w u else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hug : r (π u) = g
            · have hc : ∀ a : H, (π u = a ∧ r a = g) ↔ π u = a := by
                intro a
                constructor
                · exact And.left
                · intro h
                  subst a
                  exact ⟨rfl, hug⟩
              simp_rw [hc]
              rw [if_pos hug]
              simpa using Finset.sum_ite_eq (Finset.univ : Finset H) (π u)
                (fun _ => w u)
            · have hnone : ∀ a : H, ¬(π u = a ∧ r a = g) := by
                rintro a ⟨rfl, ha⟩
                exact hug ha
              simp [hnone, hug]

private abbrev UnitLiftData (ℓ q : ℕ) :=
  {x : (ZMod q)ˣ × Fin ℓ //
    Nat.Coprime (x.1.val.val + x.2.1 * q) ℓ}

private noncomputable def unitLiftsEquiv (ℓ q : ℕ) (hℓ : 0 < ℓ) (hq : 0 < q) :
    UnitLiftData ℓ q ≃ (ZMod (ℓ * q))ˣ := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (ℓ * q) := ⟨mul_ne_zero hℓ.ne' hq.ne'⟩
  let toFun : UnitLiftData ℓ q → (ZMod (ℓ * q))ˣ := fun x =>
    ZMod.unitOfCoprime (x.1.1.val.val + x.1.2.1 * q) <|
      x.2.mul_right <|
        (Nat.coprime_add_mul_right_left x.1.1.val.val q x.1.2.1).mpr
          (ZMod.val_coe_unit_coprime x.1.1)
  let invFun : (ZMod (ℓ * q))ˣ → UnitLiftData ℓ q := fun u => by
    let a := ZMod.unitsMap (Nat.dvd_mul_left q ℓ) u
    let b : Fin ℓ := ⟨u.val.val / q, by
      have hu_lt : u.val.val < ℓ * q := ZMod.val_lt _
      exact (Nat.div_lt_iff_lt_mul hq).mpr hu_lt⟩
    have ha_cast : (a : ZMod q) = (u.val.val : ZMod q) := by
      simp [a, ZMod.unitsMap_val]
    have ha_val : a.val.val = u.val.val % q := by
      have h := congrArg ZMod.val ha_cast
      rw [ZMod.val_natCast] at h
      exact h
    have hrepr : a.val.val + b.1 * q = u.val.val := by
      rw [ha_val]
      simpa [b, mul_comm] using Nat.mod_add_div u.val.val q
    refine ⟨(a, b), ?_⟩
    rw [hrepr]
    exact (ZMod.val_coe_unit_coprime u).of_dvd_right (Nat.dvd_mul_right ℓ q)
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨a, b⟩, hab⟩
    have ha_lt : a.val.val < q := ZMod.val_lt _
    have hb_le : b.1 + 1 ≤ ℓ := b.2
    have hx_lt : a.val.val + b.1 * q < ℓ * q := calc
      _ < q + b.1 * q := Nat.add_lt_add_right ha_lt _
      _ = (b.1 + 1) * q := by simp [Nat.add_mul, Nat.add_comm]
      _ ≤ ℓ * q := Nat.mul_le_mul_right q hb_le
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      dsimp [invFun, toFun]
      change (((a.val.val + b.1 * q : ℕ) : ZMod (ℓ * q)).cast : ZMod q) = a
      rw [ZMod.cast_eq_val]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx_lt]
      simp [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    · apply Fin.ext
      dsimp [invFun, toFun]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx_lt]
      rw [Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ha_lt, zero_add]
  · intro u
    apply Units.ext
    dsimp [invFun, toFun]
    have ha_cast :
        ((ZMod.unitsMap (Nat.dvd_mul_left q ℓ) u : (ZMod q)ˣ) : ZMod q) =
          (u.val.val : ZMod q) := by
      simp [ZMod.unitsMap_val]
    have ha_val :
        (ZMod.unitsMap (Nat.dvd_mul_left q ℓ) u).val.val = u.val.val % q := by
      have h := congrArg ZMod.val ha_cast
      rw [ZMod.val_natCast] at h
      exact h
    change (((ZMod.unitsMap (Nat.dvd_mul_left q ℓ) u).val.val +
      u.val.val / q * q : ℕ) : ZMod (ℓ * q)) = u
    rw [← ZMod.natCast_zmod_val u.val]
    congr 1
    rw [ha_val]
    simpa [mul_comm] using Nat.mod_add_div u.val.val q

private theorem exists_unique_nonunit_lift
    (a ℓ q : ℕ) (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ q) :
    ∃ b₀ c : ℕ, b₀ < ℓ ∧ a + b₀ * q = ℓ * c ∧
      ∀ b < ℓ, Nat.Coprime (a + b * q) ℓ ↔ b ≠ b₀ := by
  classical
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  have hq0 : (q : ZMod ℓ) ≠ 0 := by
    intro hz
    exact (hℓ.coprime_iff_not_dvd.mp hcop)
      ((ZMod.natCast_eq_zero_iff q ℓ).mp hz)
  let b₀ := (-((a : ZMod ℓ) * (q : ZMod ℓ)⁻¹)).val
  have hb₀ : b₀ < ℓ := ZMod.val_lt _
  have hzero : ((a + b₀ * q : ℕ) : ZMod ℓ) = 0 := by
    dsimp [b₀]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    field_simp
    ring
  have hdiv : ℓ ∣ a + b₀ * q := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨b₀, c, hb₀, hc, ?_⟩
  intro b hb
  rw [Nat.coprime_comm, hℓ.coprime_iff_not_dvd, ← ZMod.natCast_eq_zero_iff]
  constructor
  · intro hnonzero hbeq
    subst b
    exact hnonzero hzero
  · intro hbne hzero'
    apply hbne
    have hmul : ((b : ℕ) : ZMod ℓ) * q = (b₀ : ZMod ℓ) * q := by
      calc
        ((b : ℕ) : ZMod ℓ) * q = -a := by
          rw [eq_neg_iff_add_eq_zero]
          simpa [Nat.cast_add, Nat.cast_mul, add_comm] using hzero'
        _ = (b₀ : ZMod ℓ) * q := by
          rw [neg_eq_iff_add_eq_zero]
          simpa [Nat.cast_add, Nat.cast_mul, add_comm] using hzero
    have hz : ((b : ℕ) : ZMod ℓ) = b₀ := mul_right_cancel₀ hq0 hmul
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hb₀] using congrArg ZMod.val hz

private theorem unitLiftsEquiv_unitsMap
    (ℓ q : ℕ) (hℓ : 0 < ℓ) (hq : 0 < q) (x : UnitLiftData ℓ q) :
    ZMod.unitsMap (Nat.dvd_mul_left q ℓ) (unitLiftsEquiv ℓ q hℓ hq x) = x.1.1 := by
  have h := congrArg (fun y : UnitLiftData ℓ q => y.1.1)
    ((unitLiftsEquiv ℓ q hℓ hq).left_inv x)
  simpa [unitLiftsEquiv] using h

private theorem unitLiftsEquiv_val
    (ℓ q : ℕ) (hℓ : 0 < ℓ) (hq : 0 < q) (x : UnitLiftData ℓ q) :
    (unitLiftsEquiv ℓ q hℓ hq x).val.val = x.1.1.val.val + x.1.2.1 * q := by
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (ℓ * q) := ⟨mul_ne_zero hℓ.ne' hq.ne'⟩
  have ha_lt : x.1.1.val.val < q := ZMod.val_lt _
  have hb_le : x.1.2.1 + 1 ≤ ℓ := x.1.2.2
  have hx_lt : x.1.1.val.val + x.1.2.1 * q < ℓ * q := calc
    _ < q + x.1.2.1 * q := Nat.add_lt_add_right ha_lt _
    _ = (x.1.2.1 + 1) * q := by simp [Nat.add_mul, Nat.add_comm]
    _ ≤ ℓ * q := Nat.mul_le_mul_right q hb_le
  simp only [unitLiftsEquiv, Equiv.coe_fn_mk, ZMod.coe_unitOfCoprime]
  exact ZMod.val_cast_of_lt hx_lt

private def unitLiftSigmaEquiv (ℓ q : ℕ) :
    UnitLiftData ℓ q ≃
      Σ a : (ZMod q)ˣ, {b : Fin ℓ // Nat.Coprime (a.val.val + b.1 * q) ℓ} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_admissible_lifts_eq_erase
    {R : Type*} [AddCommMonoid R] (a ℓ q b₀ : ℕ) [NeZero ℓ] (hb₀ : b₀ < ℓ)
    (hadm : ∀ b < ℓ, Nat.Coprime (a + b * q) ℓ ↔ b ≠ b₀)
    (F : Fin ℓ → R) :
    (∑ b : {b : Fin ℓ // Nat.Coprime (a + b.1 * q) ℓ}, F b.1) =
      ∑ b ∈ (Finset.range ℓ).erase b₀, F (Fin.ofNat ℓ b) := by
  classical
  symm
  refine Finset.sum_bij (fun b hb => ⟨⟨b, Finset.mem_range.mp
      (Finset.mem_of_mem_erase hb)⟩, ?_⟩) ?_ ?_ ?_ ?_
  · exact (hadm b (Finset.mem_range.mp (Finset.mem_of_mem_erase hb))).mpr
      (Finset.ne_of_mem_erase hb)
  · simp
  · intro b₁ hb₁ b₂ hb₂ heq
    exact congrArg (fun x => x.1.1) heq
  · intro b _
    refine ⟨b.1.1, Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr b.1.2⟩, ?_⟩
    · exact (hadm b.1.1 b.1.2).mp b.2
    · apply Subtype.ext
      apply Fin.ext
      rfl
  · intro b hb
    congr 1
    apply Fin.ext
    simp only [Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_of_mem_erase hb))

private theorem modularSymbol_add_modulus
    {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (j : ℕ) (a m : ℚ) (hm : m ≠ 0) :
    MTT.modularSymbol f j (a + m) m = MTT.modularSymbol f j a m := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f
    (show (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods by
      simp [MTT.GammaOne, CongruenceSubgroup.strictPeriods_Gamma1])
  unfold MTT.modularSymbol MTT.modularIntegral
  apply congrArg (fun z : ℂ => (2 * Real.pi : ℂ) * z)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have harg : (-(a + m) / m : ℂ) + Complex.I * t + 1 =
      (-a / m : ℂ) + Complex.I * t := by
    push_cast
    field_simp [hmC]
    ring
  have hf :
      f (UpperHalfPlane.ofComplex ((-(a + m) / m : ℚ) + Complex.I * t)) =
      f (UpperHalfPlane.ofComplex ((-a / m : ℚ) + Complex.I * t)) := by
    have h := hp ((-(a + m) / m : ℂ) + Complex.I * t)
    change f (UpperHalfPlane.ofComplex
      ((-(a + m) / m : ℂ) + Complex.I * t + 1)) =
      f (UpperHalfPlane.ofComplex ((-(a + m) / m : ℂ) + Complex.I * t)) at h
    rw [harg] at h
    push_cast at h ⊢
    exact h.symm
  dsimp only
  rw [hf]
  congr 1
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_smul,
    Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  congr 1
  linear_combination (m : ℂ) * harg

private theorem signedModularSymbol_add_modulus
    {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (s : Bool) (j : ℕ) (a m : ℚ) (hm : m ≠ 0) :
    signedModularSymbol f s j (a + m) m = signedModularSymbol f s j a m := by
  have hneg := modularSymbol_add_modulus f j (-(a + m)) m hm
  have heq : -(a + m) + m = -a := by ring
  rw [heq] at hneg
  simp only [signedModularSymbol, modularSymbol_add_modulus f j a m hm]
  rw [← hneg]

private theorem algebraicSymbol_periodic
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (m : ℚ) (hm : m ≠ 0) :
    Function.Periodic (fun a : ℚ => MTT.algebraicSymbol P s j a m) m := by
  intro a
  apply ι.injective
  apply mul_right_cancel₀ (P.omega_ne s)
  rw [algebraicSymbol_eq_signedModularSymbol_v3 hN hk f P s j (a + m) m hj hm,
    algebraicSymbol_eq_signedModularSymbol_v3 hN hk f P s j a m hj hm]
  exact signedModularSymbol_add_modulus f.form s j a m hm

private theorem periodic_rat_congr_nat
    {T : Type*} {m : ℕ} (F : ℚ → T)
    (hF : Function.Periodic F (m : ℚ)) {a b : ℕ}
    (h : (a : ZMod m) = (b : ZMod m)) : F a = F b := by
  have hz : ((a : ℤ) : ZMod m) = ((b : ℤ) : ZMod m) := by exact_mod_cast h
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (b : ℤ) m).mp hz
  have hcQ : (b : ℚ) = (a : ℚ) + (c : ℚ) * (m : ℚ) := by
    have hcast : (b : ℚ) - (a : ℚ) = (m : ℚ) * (c : ℚ) := by exact_mod_cast hc
    linear_combination hcast
  rw [hcQ]
  exact (hF.int_mul c (a : ℚ)).symm

theorem projection_relation
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (scale : IntegralPeriodScale f ιp P)
    (Θ : SeededFiniteThetaDataV3 L)
    (s : Bool) (hΘ : Θ.IsInverseSeedThetaSystemForSign P scale s)
    (A : Finset ℕ) (n : ℕ) (hn : n ∉ A) :
    MonoidAlgebra.mapRingHom
        (HorizontalFiniteGroup p L.exponent A) Θ.coefficientRing.subtype
        (horizontalGroupAlgebraProjection Θ.coefficientRing
          (Finset.subset_insert n A) (Θ.theta (insert n A))) =
      inverseSeedEulerFactorCp Θ.characters A n hn *
        MonoidAlgebra.mapRingHom
          (HorizontalFiniteGroup p L.exponent A) Θ.coefficientRing.subtype
          (Θ.theta A) := by
  classical
  let j := k / 2 - 1
  have hj : j ≤ k - 2 := by omega
  have hcentral : 2 * j = k - 2 := by
    obtain ⟨r, rfl⟩ := heven
    omega
  letI : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  rcases hΘ with ⟨htheta, heuler⟩
  let ℓ := L.primeAt n
  let M := L.supportModulus A
  let q := η.2.conductor * M
  have hℓ : ℓ.Prime := L.primeAt_prime n
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hM : 0 < M := L.supportModulus_pos A
  have hq : 0 < q := mul_pos (Nat.pos_of_ne_zero η.2.conductor_ne_zero) hM
  have hcopD : Nat.Coprime ℓ η.2.conductor := by
    exact (L.primeAt_orderly n).2.2.1.of_dvd_right (Nat.dvd_mul_left _ _)
  have hcopM : Nat.Coprime ℓ M := L.primeAt_coprime_supportModulus A n hn
  have hcopq : Nat.Coprime ℓ q := hcopD.mul_right hcopM
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (ℓ * q) := ⟨mul_ne_zero hℓ.ne_zero hq.ne'⟩
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  obtain ⟨G, rfl⟩ := horizontalRestrictionHom_surjective
    (p := p) (m := L.exponent) (Finset.subset_insert n A) g
  let M' := L.supportModulus (insert n A)
  let q' := η.2.conductor * M'
  letI : NeZero q' := ⟨mul_ne_zero η.2.conductor_ne_zero
    (Nat.ne_of_gt (L.supportModulus_pos (insert n A)))⟩
  let π' : (ZMod q')ˣ → HorizontalFiniteGroup p L.exponent (insert n A) :=
    fun u => Θ.characters.projections.supportProjection (insert n A)
      (ZMod.unitsMap (Nat.dvd_mul_left M' η.2.conductor) u)
  let w' : (ZMod q')ˣ → ℂ_[p] := fun u =>
    ιp (scale.scale * η.2 u.val.val *
      MTT.algebraicSymbol P s (k / 2 - 1) u.val.val q' /
        (M' : MTT.Qbar) ^ (k / 2 - 1))
  have hM'eq : M' = ℓ * M := by
    simpa [M', M, ℓ] using supportModulus_insert L A n hn
  have hq'eq : q' = ℓ * q := by
    simp only [q', q, hM'eq]
    ac_rfl
  subst M'
  subst q'
  let E : UnitLiftData ℓ q ≃
      (ZMod (η.2.conductor * L.supportModulus (insert n A)))ˣ :=
    (unitLiftsEquiv ℓ q hℓ.pos hq).trans
      (Units.mapEquiv (ZMod.ringEquivCongr hq'eq.symm).toMulEquiv).toEquiv
  have hEval (x : UnitLiftData ℓ q) :
      (E x).val.val = x.1.1.val.val + x.1.2.1 * q := by
    let v := unitLiftsEquiv ℓ q hℓ.pos hq x
    change (ZMod.ringEquivCongr hq'eq.symm (v : ZMod (ℓ * q))).val = _
    rw [← ZMod.natCast_zmod_val (v : ZMod (ℓ * q)), map_natCast,
      ZMod.val_natCast, hq'eq, Nat.mod_eq_of_lt (ZMod.val_lt (v : ZMod (ℓ * q)))]
    exact unitLiftsEquiv_val ℓ q hℓ.pos hq x
  have hMM' : M ∣ L.supportModulus (insert n A) := by
    rw [hM'eq]
    exact Nat.dvd_mul_left M ℓ
  have hproj (x : UnitLiftData ℓ q) :
      horizontalRestrictionHom (Finset.subset_insert n A) (π' (E x)) =
        Θ.characters.projections.supportProjection A
          (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) x.1.1) := by
    have hqq' : q ∣ η.2.conductor * L.supportModulus (insert n A) := by
      rw [hq'eq]
      exact Nat.dvd_mul_left q ℓ
    have hmap : ZMod.unitsMap hqq' (E x) = x.1.1 := by
      apply Units.ext
      let v := unitLiftsEquiv ℓ q hℓ.pos hq x
      have hv := congrArg Units.val (unitLiftsEquiv_unitsMap ℓ q hℓ.pos hq x)
      change ((ZMod.ringEquivCongr hq'eq.symm (v : ZMod (ℓ * q))).cast : ZMod q) = x.1.1
      rw [← ZMod.natCast_zmod_val (v : ZMod (ℓ * q))]
      simp only [map_natCast, ZMod.cast_eq_val, ZMod.val_natCast]
      rw [hq'eq, Nat.mod_eq_of_lt (ZMod.val_lt (v : ZMod (ℓ * q)))]
      simpa only [v, ZMod.unitsMap_val, ZMod.cast_eq_val] using hv
    rw [supportProjection_restrict Θ.characters.projections
      (Finset.subset_insert n A) hMM']
    congr 1
    calc
      ZMod.unitsMap hMM'
          (ZMod.unitsMap (Nat.dvd_mul_left
            (L.supportModulus (insert n A)) η.2.conductor) (E x)) =
          ZMod.unitsMap (dvd_trans hMM'
            (Nat.dvd_mul_left (L.supportModulus (insert n A)) η.2.conductor)) (E x) :=
        DFunLike.congr_fun (ZMod.unitsMap_comp hMM'
          (Nat.dvd_mul_left (L.supportModulus (insert n A)) η.2.conductor)) (E x)
      _ = ZMod.unitsMap (dvd_trans (Nat.dvd_mul_left M η.2.conductor) hqq') (E x) := by
        rfl
      _ = ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor)
          (ZMod.unitsMap hqq' (E x)) :=
        (DFunLike.congr_fun (ZMod.unitsMap_comp
          (Nat.dvd_mul_left M η.2.conductor) hqq') (E x)).symm
      _ = ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) x.1.1 := by rw [hmap]
  have hleft := mapDomain_coefficient_of_formula
    Θ.coefficientRing.subtype.toAddMonoidHom (Θ.theta (insert n A)).coeff π'
    (horizontalRestrictionHom (Finset.subset_insert n A))
    ((horizontalRestrictionHom (Finset.subset_insert n A)) G) w'
    (htheta (insert n A))
  simp only [MonoidAlgebra.coeff_mapRingHom]
  simp only [inverseSeedEulerFactorCp, sub_mul]
  simp [MonoidAlgebra.coeff_single_mul_apply]
  rw [htheta A ((horizontalRestrictionHom (Finset.subset_insert n A)) G),
    htheta A ((Θ.characters.horizontalPrimeElement A n hn)⁻¹ *
      (horizontalRestrictionHom (Finset.subset_insert n A)) G),
    htheta A (Θ.characters.horizontalPrimeElement A n hn *
      (horizontalRestrictionHom (Finset.subset_insert n A)) G)]
  simp only [horizontalGroupAlgebraProjection,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
  change Θ.coefficientRing.subtype.toAddMonoidHom
    ((Finsupp.mapDomain (⇑(horizontalRestrictionHom (Finset.subset_insert n A)))
      (Θ.theta (insert n A)).coeff)
      ((horizontalRestrictionHom (Finset.subset_insert n A)) G)) = _
  rw [hleft]
  calc
    (∑ u, if horizontalRestrictionHom (Finset.subset_insert n A) (π' u) =
          horizontalRestrictionHom (Finset.subset_insert n A) G then w' u else 0) =
        ∑ x : UnitLiftData ℓ q,
          if horizontalRestrictionHom (Finset.subset_insert n A) (π' (E x)) =
            horizontalRestrictionHom (Finset.subset_insert n A) G then w' (E x) else 0 := by
      exact Fintype.sum_equiv E.symm _ _ (fun x =>
        congrArg (fun y => if horizontalRestrictionHom (Finset.subset_insert n A) (π' y) =
          horizontalRestrictionHom (Finset.subset_insert n A) G then w' y else 0)
          (E.apply_symm_apply x).symm)
    _ = _ := by
      simp_rw [hproj]
      simp only [w']
      simp_rw [hEval]
      let C : (ZMod q)ˣ → Prop := fun a =>
        Θ.characters.projections.supportProjection A
            (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) a) =
          horizontalRestrictionHom (Finset.subset_insert n A) G
      let Φ : (ZMod q)ˣ → Fin ℓ → ℂ_[p] := fun a b =>
        ιp (scale.scale * η.2 (a.val.val + b.1 * q) *
          MTT.algebraicSymbol P s (k / 2 - 1) (a.val.val + b.1 * q)
            (η.2.conductor * L.supportModulus (insert n A)) /
          (L.supportModulus (insert n A) : MTT.Qbar) ^ (k / 2 - 1))
      calc
        _ = (∑ x : UnitLiftData ℓ q,
              if C x.1.1 then Φ x.1.1 x.1.2 else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : C x.1.1 <;>
            simp [C, Φ, hx, Nat.cast_add, Nat.cast_mul]
        _ =
            ∑ y : Σ a : (ZMod q)ˣ,
              {b : Fin ℓ // Nat.Coprime (a.val.val + b.1 * q) ℓ},
              if C y.1 then Φ y.1 y.2.1 else 0 := by
          exact Fintype.sum_equiv (unitLiftSigmaEquiv ℓ q) _ _ (fun _ => rfl)
        _ = ∑ a : (ZMod q)ˣ, ∑ b :
              {b : Fin ℓ // Nat.Coprime (a.val.val + b.1 * q) ℓ},
              if C a then Φ a b.1 else 0 := Fintype.sum_sigma _
        _ = _ := by
          let uℓ : (ZMod q)ˣ := ZMod.unitOfCoprime ℓ hcopq
          let V : ℕ → ℂ_[p] := fun a =>
            ιp (scale.scale * η.2 a *
              MTT.algebraicSymbol P s j a q / (M : MTT.Qbar) ^ j)
          let W : (ZMod q)ˣ → ℂ_[p] := fun a => V a.val.val
          have hVcongr {a b : ℕ} (hab : (a : ZMod q) = (b : ZMod q)) :
              V a = V b := by
            have hD : (a : ZMod η.2.conductor) = (b : ZMod η.2.conductor) := by
              rw [ZMod.natCast_eq_natCast_iff] at hab ⊢
              exact hab.of_dvd (Nat.dvd_mul_right η.2.conductor M)
            have hlevel : (a : ZMod η.1.1) = (b : ZMod η.1.1) := by
              rw [← hηprim]
              exact hD
            have hη : η.2 a = η.2 b := congrArg η.2 hlevel
            have hper := algebraicSymbol_periodic hN hk f P s j hj (q : ℚ)
              (by exact_mod_cast hq.ne')
            have hsym := periodic_rat_congr_nat
              (fun x : ℚ => MTT.algebraicSymbol P s j x q) hper hab
            simp only [V, hη, hsym]
          have hinner (a : (ZMod q)ˣ) :
              (∑ b : {b : Fin ℓ // Nat.Coprime (a.val.val + b.1 * q) ℓ},
                if C a then Φ a b.1 else 0) =
                ιp (f.coeff ℓ) / (ℓ : ℂ_[p]) ^ j *
                    (if C a then W a else 0) -
                  ιp (η.2 ℓ) * (if C a then W (uℓ⁻¹ * a) else 0) -
                  ιp (f.epsilon ℓ) * (ιp (η.2 ℓ))⁻¹ *
                    (if C a then W (uℓ * a) else 0) := by
            by_cases hCa : C a
            · obtain ⟨b₀, c, hb₀, hlift, hadm⟩ :=
                exists_unique_nonunit_lift a.val.val ℓ q hℓ hcopq
              simp only [hCa, if_true]
              rw [sum_admissible_lifts_eq_erase a.val.val ℓ q b₀ hb₀ hadm]
              have hc_lt : c < q := by
                apply (Nat.mul_lt_mul_left hℓ.pos).mp
                rw [← hlift]
                calc
                  a.val.val + b₀ * q < q + b₀ * q :=
                    Nat.add_lt_add_right (ZMod.val_lt a.val) _
                  _ = (b₀ + 1) * q := by simp [Nat.add_mul, Nat.add_comm]
                  _ ≤ ℓ * q := Nat.mul_le_mul_right q hb₀
              have hcCop : c.Coprime q := by
                have hp : (ℓ * c).Coprime q := by
                  rw [← hlift, Nat.coprime_add_mul_right_left]
                  exact ZMod.val_coe_unit_coprime a
                exact (Nat.coprime_mul_iff_left.mp hp).2
              have hu : uℓ⁻¹ * a = ZMod.unitOfCoprime c hcCop := by
                apply (mul_left_cancel (a := uℓ))
                simp only [mul_inv_cancel_left]
                apply Units.ext
                simp only [Units.val_mul]
                change (a : ZMod q) = (uℓ : ZMod q) * (c : ZMod q)
                simp only [uℓ, ZMod.coe_unitOfCoprime]
                rw [← ZMod.natCast_zmod_val (a : ZMod q)]
                rw [← Nat.cast_mul, ← hlift]
                simp [Nat.cast_add, Nat.cast_mul]
              have hcval : (uℓ⁻¹ * a).val.val = c := by
                rw [hu]
                simp [ZMod.val_natCast, Nat.mod_eq_of_lt hc_lt]
              have hmulmod :
                  (((uℓ * a).val.val : ℕ) : ZMod q) =
                    ((ℓ * a.val.val : ℕ) : ZMod q) := by
                calc
                  (((uℓ * a).val.val : ℕ) : ZMod q) =
                      (uℓ * a : ZMod q) := ZMod.natCast_zmod_val _
                  _ = ((ℓ * a.val.val : ℕ) : ZMod q) := by
                    rw [← ZMod.natCast_zmod_val (a : ZMod q)]
                    simp [uℓ, Nat.cast_mul]
              have hWinv : W (uℓ⁻¹ * a) = V c := by
                change V (uℓ⁻¹ * a).val.val = V c
                exact congrArg V hcval
              have hWmul : W (uℓ * a) = V (ℓ * a.val.val) := by
                exact hVcongr hmulmod
              have hηlift (b : ℕ) :
                  η.2 (a.val.val + b * q) = η.2 a.val.val := by
                apply congrArg η.2
                rw [← hηprim]
                simp [q, Nat.cast_add, Nat.cast_mul]
              have hηac : η.2 a.val.val = η.2 ℓ * η.2 c := by
                rw [← hηlift b₀]
                have hlift' :
                    ((a.val.val + b₀ * q : ℕ) : ZMod η.1.1) =
                      ((ℓ * c : ℕ) : ZMod η.1.1) := by
                  exact congrArg (fun z : ℕ => (z : ZMod η.1.1)) hlift
                push_cast at hlift'
                have h := congrArg η.2 hlift'
                simpa only [map_mul] using h
              have hηmul : η.2 (ℓ * a.val.val) = η.2 ℓ * η.2 a.val.val := by
                simp only [Nat.cast_mul, map_mul]
              have hηℓ_ne : η.2 ℓ ≠ 0 := by
                have hcop' : IsCoprime (ℓ : ℤ) (η.1.1 : ℤ) := by
                  rw [← hηprim]
                  exact_mod_cast hcopD
                simpa using
                  (DirichletCharacter.apply_ne_zero_iff η.2 (ℓ : ℤ)).2 hcop'
              have hdist := MTT.algebraicSymbol_horizontal_unitFiber_distribution
                hN hk ι f P s j hj hcentral ℓ q hℓ hq hcopq
                a.val.val c b₀ hb₀ hlift
              have hscaled := congrArg
                (fun z : MTT.Qbar =>
                  scale.scale * η.2 a.val.val *
                    (η.2.conductor : MTT.Qbar) ^ j * z) hdist
              have hD0 : (η.2.conductor : MTT.Qbar) ≠ 0 := by
                exact_mod_cast η.2.conductor_ne_zero
              have hM0 : (M : MTT.Qbar) ≠ 0 := by exact_mod_cast hM.ne'
              have hℓ0 : (ℓ : MTT.Qbar) ≠ 0 := by exact_mod_cast hℓ.ne_zero
              have hraw :
                  (∑ b ∈ (Finset.range ℓ).erase b₀,
                    scale.scale * η.2 (a.val.val + b * q) *
                      MTT.algebraicSymbol P s j
                        ((a.val.val : ℚ) + (b : ℚ) * (q : ℚ))
                        ((η.2.conductor : ℚ) *
                          (L.supportModulus (insert n A) : ℚ)) /
                      (L.supportModulus (insert n A) : MTT.Qbar) ^ j) =
                    f.coeff ℓ / (ℓ : MTT.Qbar) ^ j *
                        (scale.scale * η.2 a.val.val *
                          MTT.algebraicSymbol P s j a.val.val q /
                          (M : MTT.Qbar) ^ j) -
                      η.2 ℓ *
                        (scale.scale * η.2 c *
                          MTT.algebraicSymbol P s j c q /
                          (M : MTT.Qbar) ^ j) -
                      f.epsilon ℓ * (η.2 ℓ)⁻¹ *
                        (scale.scale * η.2 (ℓ * a.val.val) *
                          MTT.algebraicSymbol P s j (ℓ * a.val.val) q /
                          (M : MTT.Qbar) ^ j) := by
                convert hscaled using 1
                · rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro b hb
                  rw [hηlift b, hM'eq]
                  simp only [Nat.cast_mul]
                  have hmod :
                      ((η.2.conductor : ℚ) * ((ℓ : ℚ) * (M : ℚ))) =
                        (ℓ : ℚ) * (q : ℚ) := by
                    simp only [q]
                    push_cast
                    ring
                  rw [hmod]
                  simp only [q]
                  push_cast
                  field_simp [hD0, hM0, hℓ0]
                  <;> ring
                · rw [hηmul, hηac]
                  simp only [q]
                  push_cast
                  field_simp [hD0, hM0, hℓ0, hηℓ_ne]
                  <;> ring
              have hmapped := congrArg ιp hraw
              simp only [map_add, map_mul, map_sub, map_div, map_pow,
                map_inv₀, map_natCast, map_sum] at hmapped
              have hcoeff :
                  ιp (f.coeff ℓ / (ℓ : MTT.Qbar) ^ j) =
                    ιp (f.coeff ℓ) / (ℓ : ℂ_[p]) ^ j := by
                simp only [div_eq_mul_inv, map_mul, map_inv₀, map_pow, map_natCast]
              rw [hcoeff, ← hηmul] at hmapped
              have hmodval : ∀ b ∈ (Finset.range ℓ).erase b₀, b % ℓ = b := by
                intro b hb
                exact Nat.mod_eq_of_lt
                  (Finset.mem_range.mp (Finset.mem_of_mem_erase hb))
              rw [hWinv, hWmul]
              simp only [Φ, V, W, Fin.val_ofNat, j]
              convert hmapped using 1
              · apply Finset.sum_congr rfl
                intro b hb
                rw [hmodval b hb]
              · simp only [j]
                push_cast
                rfl
            · simp [hCa]
          rw [Finset.sum_congr rfl (fun a _ => hinner a),
            Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          have hsecond :
              (∑ a : (ZMod q)ˣ, if C a then W (uℓ⁻¹ * a) else 0) =
                ∑ u : (ZMod q)ˣ,
                  if Θ.characters.projections.supportProjection A
                      (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) u) =
                      (Θ.characters.horizontalPrimeElement A n hn)⁻¹ *
                        horizontalRestrictionHom (Finset.subset_insert n A) G then
                    W u else 0 := by
            have huℓ :
                Θ.characters.projections.supportProjection A
                    (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) uℓ) =
                  Θ.characters.horizontalPrimeElement A n hn := by
              apply congrArg (Θ.characters.projections.supportProjection A)
              apply Units.ext
              simp [uℓ, q, ℓ,
                SeededHorizontalCharacterRealizationV3.horizontalPrimeElement,
                ZMod.unitsMap_val]
            calc
              _ = ∑ u : (ZMod q)ˣ,
                    if C (uℓ * u) then W (uℓ⁻¹ * (uℓ * u)) else 0 :=
                (Equiv.sum_comp (Equiv.mulLeft uℓ)
                  (fun a : (ZMod q)ˣ => if C a then W (uℓ⁻¹ * a) else 0)).symm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro u _
                simp only [inv_mul_cancel_left]
                simp only [C, map_mul, huℓ]
                apply if_congr
                · exact eq_inv_mul_iff_mul_eq.symm
                · rfl
                · rfl
          have hthird :
              (∑ a : (ZMod q)ˣ, if C a then W (uℓ * a) else 0) =
                ∑ u : (ZMod q)ˣ,
                  if Θ.characters.projections.supportProjection A
                      (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) u) =
                      Θ.characters.horizontalPrimeElement A n hn *
                        horizontalRestrictionHom (Finset.subset_insert n A) G then
                    W u else 0 := by
            have huℓ :
                Θ.characters.projections.supportProjection A
                    (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) uℓ) =
                  Θ.characters.horizontalPrimeElement A n hn := by
              apply congrArg (Θ.characters.projections.supportProjection A)
              apply Units.ext
              simp [uℓ, q, ℓ, ZMod.unitsMap_val]
            have huℓinv :
                Θ.characters.projections.supportProjection A
                    (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) uℓ⁻¹) =
                  (Θ.characters.horizontalPrimeElement A n hn)⁻¹ := by
              rw [map_inv, map_inv, huℓ]
            calc
              _ = ∑ u : (ZMod q)ˣ,
                    if C (uℓ⁻¹ * u) then W (uℓ * (uℓ⁻¹ * u)) else 0 :=
                (Equiv.sum_comp (Equiv.mulLeft uℓ⁻¹)
                  (fun a : (ZMod q)ˣ => if C a then W (uℓ * a) else 0)).symm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro u _
                simp only [mul_inv_cancel_left]
                simp only [C, map_mul, huℓinv]
                apply if_congr
                · exact inv_mul_eq_iff_eq_mul
                · rfl
                · rfl
          rw [hsecond, hthird]

end HorizontalPadicL.AnyParityProjection


open scoped BigOperators

namespace HorizontalPadicL.AnyParityEvaluation

lemma changeLevel_natCast_aux {R : Type*} [CommMonoidWithZero R] {n m : ℕ}
    (χ : DirichletCharacter R n) (hm : n ∣ m) (z : ℕ) (hz : z.Coprime m) :
    DirichletCharacter.changeLevel hm χ (z : ZMod m) = χ (z : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hm (a := (z : ℤ))
    (Nat.isCoprime_iff_coprime.mpr hz)
  simpa using this

lemma conductor_dvd_of_mul_aux {R : Type*} [CommMonoidWithZero R] {a b L : ℕ}
    [NeZero a] [NeZero L]
    (χ : DirichletCharacter R a) (ψ : DirichletCharacter R b) (φ : DirichletCharacter R L)
    (hab : a.Coprime b) (hLab : L ∣ a * b)
    (hφ : ∀ z : ℕ, z.Coprime L → φ (z : ZMod L) = χ (z : ZMod a) * ψ (z : ZMod b)) :
    χ.conductor ∣ φ.conductor := by
  set c := φ.conductor with hc
  suffices h : χ.FactorsThrough (a.gcd c) from
    (DirichletCharacter.conductor_dvd_of_mem_conductorSet χ h).trans (Nat.gcd_dvd_right a c)
  refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_left a c)).mpr
    fun x hx ↦ MonoidHom.mem_ker.mpr ?_
  rw [Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  have hx' : x.val.val ≡ 1 [MOD a.gcd c] := by
    rwa [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
      Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hx
  obtain ⟨z, hza, hzb⟩ := Nat.chineseRemainder hab x.val.val 1
  have hzc : (z : ℕ) ≡ 1 [MOD c] := by
    have h1 : (z : ℕ) ≡ 1 [MOD a.gcd c] := (hza.of_dvd (Nat.gcd_dvd_left a c)).trans hx'
    have hcop : (a.gcd c).Coprime b := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a c) hab
    have h2 : (z : ℕ) ≡ 1 [MOD a.gcd c * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, hzb⟩
    have hcd : c ∣ a.gcd c * b := by
      rw [← Nat.gcd_mul_right]
      exact Nat.dvd_gcd ((DirichletCharacter.conductor_dvd_level φ).trans hLab)
        (dvd_mul_right c b)
    exact h2.of_dvd hcd
  have hzL : (z : ℕ).Coprime L := by
    have hxa : x.val.val.Coprime a := ZMod.val_coe_unit_coprime x
    have hza' : (z : ℕ).Coprime a := by
      unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hza]; exact hxa
    have hzb' : (z : ℕ).Coprime b := by
      unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hzb]; simp
    exact Nat.Coprime.coprime_dvd_right hLab (Nat.Coprime.mul_right hza' hzb')
  have hφz : φ ((z : ℕ) : ZMod L) = 1 := by
    obtain ⟨hdvd, φ₀, hφ₀⟩ := φ.factorsThrough_conductor
    rw [hφ₀, changeLevel_natCast_aux φ₀ hdvd _ hzL]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hzc, Nat.cast_one, map_one]
  have hχz : ((z : ℕ) : ZMod a) = x.val := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hza, ZMod.natCast_zmod_val]
  have hψz : ((z : ℕ) : ZMod b) = 1 := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hzb, Nat.cast_one]
  rw [hφ z hzL, hχz, hψz, map_one, mul_one] at hφz
  exact hφz

lemma conductor_mul_of_coprime_aux {R : Type*} [CommMonoidWithZero R] {a b : ℕ}
    [NeZero a] [NeZero b]
    (χ : DirichletCharacter R a) (ψ : DirichletCharacter R b)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hab : a.Coprime b) :
    (χ.mul ψ).conductor = a * b := by
  have hL : Nat.lcm a b = a * b := Nat.Coprime.lcm_eq_mul hab
  have : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hφ : ∀ z : ℕ, z.Coprime (Nat.lcm a b) →
      χ.mul ψ (z : ZMod (Nat.lcm a b)) = χ (z : ZMod a) * ψ (z : ZMod b) := by
    intro z hz
    rw [DirichletCharacter.mul, MulChar.mul_apply, changeLevel_natCast_aux _ _ _ hz,
      changeLevel_natCast_aux _ _ _ hz]
  have h1 := conductor_dvd_of_mul_aux χ ψ (χ.mul ψ) hab hL.dvd hφ
  have h2 := conductor_dvd_of_mul_aux ψ χ (χ.mul ψ) hab.symm (by rw [hL, mul_comm])
    (fun z hz => by rw [hφ z hz, mul_comm])
  rw [hχ] at h1
  rw [hψ] at h2
  apply Nat.dvd_antisymm _ (Nat.Coprime.mul_dvd_of_dvd_of_dvd hab h1 h2)
  rw [← hL]
  exact DirichletCharacter.conductor_dvd_level _

lemma primitiveProductV2_spec_aux (η ψ : DirichletCharacterWithLevel)
    (hη : η.2.IsPrimitive) (hψ : ψ.2.IsPrimitive) (hcop : η.1.1.Coprime ψ.1.1) :
    (primitiveProductV2 η ψ).1.1 = η.1.1 * ψ.1.1 ∧
      ∀ z : ℕ, z.Coprime (η.1.1 * ψ.1.1) →
        (primitiveProductV2 η ψ).2 (z : ZMod (primitiveProductV2 η ψ).1.1) =
          η.2 (z : ZMod η.1.1) * ψ.2 (z : ZMod ψ.1.1) := by
  have : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  have : NeZero ψ.1.1 := ⟨Nat.ne_of_gt ψ.1.2⟩
  have hL : Nat.lcm η.1.1 ψ.1.1 = η.1.1 * ψ.1.1 := Nat.Coprime.lcm_eq_mul hcop
  have hc := conductor_mul_of_coprime_aux η.2 ψ.2 hη hψ hcop
  unfold primitiveProductV2
  dsimp only
  refine ⟨hc, fun z hz => ?_⟩
  have hz' : IsCoprime (z : ℤ) (Nat.lcm η.1.1 ψ.1.1 : ℕ) := by
    rw [hL]; exact Nat.isCoprime_iff_coprime.mpr hz
  have := DirichletCharacter.primitiveCharacter_apply_of_isCoprime (η.2.mul ψ.2) hz'
  simp only [Int.cast_natCast] at this
  rw [this, DirichletCharacter.mul, MulChar.mul_apply,
    changeLevel_natCast_aux _ _ _ (hL ▸ hz), changeLevel_natCast_aux _ _ _ (hL ▸ hz)]

lemma sum_zmod_eq_sum_units_aux {c : ℕ} [NeZero c] (T : DirichletCharacter MTT.Qbar c)
    (F : ℕ → MTT.Qbar) :
    ∑ a : ZMod c, T a * F a.val = ∑ u : (ZMod c)ˣ, T u * F (u : ZMod c).val := by
  classical
  refine Eq.trans ?_ (Finset.sum_map (Finset.univ : Finset (ZMod c)ˣ)
    ⟨((↑) : (ZMod c)ˣ → ZMod c), Units.val_injective⟩ (fun a => T a * F a.val))
  refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
  have hu : ¬ IsUnit a := by
    rintro ⟨u, rfl⟩
    exact ha (Finset.mem_map_of_mem _ (Finset.mem_univ u))
  rw [MulChar.map_nonunit T hu, zero_mul]

lemma sum_units_congr_level_aux {c q : ℕ} [NeZero c] [NeZero q] (h : c = q)
    (F : ℕ → ℕ → MTT.Qbar) :
    ∑ u : (ZMod c)ˣ, F c (u : ZMod c).val = ∑ u : (ZMod q)ˣ, F q (u : ZMod q).val := by
  subst h; rfl

/-- Evaluation of an inverse-seed theta element at a full-support horizontal
character has the same zero set as the corresponding algebraic modular-symbol
sum.  The supplied equality is the small level-change bridge identifying the
full-level character with its primitive realization. -/
theorem eval_ne_zero_iff
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hk : 2 ≤ k) (heven : Even k)
    (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (scale : IntegralPeriodScale f ιp P)
    (Θ : SeededFiniteThetaDataV3 L)
    (s : Bool) (hΘ : Θ.IsInverseSeedThetaSystemForSign P scale s)
    (χ : HorizontalCharacter p L.exponent)
    (hfull : (Θ.characters.realized χ).2.conductor =
      L.supportModulus χ.support)
    (hatLevel : ∀ u : (ZMod (L.supportModulus χ.support))ˣ,
      Θ.characters.atLevel χ u.val.val =
        (Θ.characters.realized χ).2 u.val.val) :
      (Θ.eval χ ≠ 0 ↔
        let θ := primitiveProductV2 η (Θ.characters.realized χ)
        letI : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
        (∑ a : ZMod θ.1.1,
          θ.2 a * MTT.algebraicSymbol P s
            (k / 2 - 1) a.val θ.1.1) ≠ 0) := by
  obtain ⟨hcoeff, -⟩ := hΘ
  set A := χ.support with hA
  set M := L.supportModulus A with hM
  set ψ := Θ.characters.realized χ with hψ
  have hMpos : 0 < M := L.supportModulus_pos A
  have hψlev : ψ.1.1 = M := by
    have := Θ.characters.realized_primitive χ
    rw [← hfull]; exact this.symm
  have hηlev : η.1.1 = η.2.conductor := hηprim.symm
  have hcop : η.1.1.Coprime M := by
    rw [hM, SeededHorizontalPrimeDataV3.supportModulus]
    refine Nat.Coprime.prod_right fun n _ => ?_
    have h := (L.primeAt_orderly n).2.2.1
    rw [hηlev]
    exact (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) h).symm
  have : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  have hq0 : η.2.conductor * M ≠ 0 :=
    mul_ne_zero η.2.conductor_ne_zero (Nat.ne_of_gt hMpos)
  have : NeZero (η.2.conductor * M) := ⟨hq0⟩
  have : NeZero ψ.1.1 := ⟨Nat.ne_of_gt ψ.1.2⟩
  have : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hχval : ∀ u : (ZMod (η.2.conductor * M))ˣ,
      χ.toMonoidHom (Θ.characters.projections.supportProjection A
        (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) u)) =
        ιp (ψ.2 ((u : ZMod (η.2.conductor * M)).val : ZMod ψ.1.1)) := by
    intro u
    rw [← Θ.characters.atLevel_compatibility χ]
    congr 1
    rw [← ZMod.natCast_zmod_val ((ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) u :
      (ZMod M)ˣ) : ZMod M), hatLevel]
    congr 1
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    exact (Nat.mod_modEq _ M).of_dvd (hψlev ▸ dvd_refl _)
  have heval : Θ.eval χ = ιp (scale.scale / (M : MTT.Qbar) ^ (k / 2 - 1) *
      ∑ u : (ZMod (η.2.conductor * M))ˣ,
        η.2 (u.val.val : ZMod η.1.1) * ψ.2 (u.val.val : ZMod ψ.1.1) *
          MTT.algebraicSymbol P s (k / 2 - 1) u.val.val (η.2.conductor * M : ℕ)) := by
    unfold SeededFiniteThetaDataV3.eval
    rw [Finsupp.sum_fintype _ _ (by simp)]
    have hc : ∀ g, (((Θ.theta A).coeff g : Θ.coefficientRing) : ℂ_[p]) =
        ∑ u : (ZMod (η.2.conductor * M))ˣ,
          if Θ.characters.projections.supportProjection A
              (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) u) = g then
            ιp (scale.scale * η.2 u.val.val *
              MTT.algebraicSymbol P s (k / 2 - 1) u.val.val (η.2.conductor * M : ℕ) /
                (M : MTT.Qbar) ^ (k / 2 - 1))
          else 0 := fun g => hcoeff A g
    refine (Finset.sum_congr rfl fun g _ =>
      congrArg (· * χ.toMonoidHom g) (hc g)).trans ?_
    rw [Finset.sum_congr rfl fun g _ => Finset.sum_mul _ _ _]
    rw [Finset.sum_comm]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hχval u, ← map_mul]
    congr 1
    ring
  have hψprim : ψ.2.IsPrimitive := Θ.characters.realized_primitive χ
  obtain ⟨hθlev, hθval⟩ := primitiveProductV2_spec_aux η ψ hηprim hψprim (hψlev ▸ hcop)
  have : NeZero (primitiveProductV2 η ψ).1.1 := ⟨Nat.ne_of_gt (primitiveProductV2 η ψ).1.2⟩
  have hθlev' : (primitiveProductV2 η ψ).1.1 = η.2.conductor * M := by
    rw [hθlev, hψlev]
    exact congrArg (· * M) hηlev
  have hT : ∀ u : (ZMod (primitiveProductV2 η ψ).1.1)ˣ,
      (primitiveProductV2 η ψ).2 u =
        η.2 ((u : ZMod (primitiveProductV2 η ψ).1.1).val : ZMod η.1.1) *
          ψ.2 ((u : ZMod (primitiveProductV2 η ψ).1.1).val : ZMod ψ.1.1) := by
    intro u
    conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod (primitiveProductV2 η ψ).1.1)]
    have hcp : ∀ x a b : ℕ, a = b → x.Coprime a → x.Coprime b := fun _ _ _ h hx => h ▸ hx
    exact hθval _ (hcp _ _ _ hθlev (ZMod.val_coe_unit_coprime u))
  have hRHS : (∑ a : ZMod (primitiveProductV2 η ψ).1.1, (primitiveProductV2 η ψ).2 a *
        MTT.algebraicSymbol P s (k / 2 - 1) a.val (primitiveProductV2 η ψ).1.1) =
      ∑ u : (ZMod (η.2.conductor * M))ˣ,
        η.2 (u.val.val : ZMod η.1.1) * ψ.2 (u.val.val : ZMod ψ.1.1) *
          MTT.algebraicSymbol P s (k / 2 - 1) u.val.val (η.2.conductor * M : ℕ) := by
    rw [sum_zmod_eq_sum_units_aux _
      (fun n => MTT.algebraicSymbol P s (k / 2 - 1) n (primitiveProductV2 η ψ).1.1)]
    simp_rw [hT]
    exact sum_units_congr_level_aux hθlev'
      (fun c n => η.2 (n : ZMod η.1.1) * ψ.2 (n : ZMod ψ.1.1) *
        MTT.algebraicSymbol P s (k / 2 - 1) n c)
  have hC : scale.scale / (M : MTT.Qbar) ^ (k / 2 - 1) ≠ 0 :=
    div_ne_zero scale.scale_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hMpos)))
  dsimp only
  rw [hRHS, heval, map_ne_zero, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hC, h⟩⟩

end HorizontalPadicL.AnyParityEvaluation





namespace HorizontalPadicL.AnyParityNorms

private theorem mapRange_subtype_injective
    {p : ℕ} [Fact p.Prime] (R : Subring ℂ_[p]) (G : Type*) [Monoid G] :
    Function.Injective (MonoidAlgebra.mapRingHom G R.subtype) := by
  intro x y hxy
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply Subtype.ext
  have hg := congrArg (fun z : MonoidAlgebra ℂ_[p] G => z.coeff g) hxy
  rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom] at hg
  exact hg

theorem normRelations
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (scale : IntegralPeriodScale f ιp P)
    (Θ : SeededFiniteThetaDataV3 L)
    (s : Bool) (hΘ : Θ.IsInverseSeedThetaSystemForSign P scale s) :
    Θ.SatisfiesNormRelations := by
  rcases hΘ with ⟨htheta, heuler⟩
  intro A n hn
  apply mapRange_subtype_injective Θ.coefficientRing
    (HorizontalFiniteGroup p L.exponent A)
  rw [map_mul, heuler A n hn]
  exact AnyParityProjection.projection_relation hN hk heven f P η hηprim ιp L scale Θ
    s ⟨htheta, heuler⟩ A n hn

end HorizontalPadicL.AnyParityNorms

namespace HorizontalPadicL

/-- The finite theta construction uses the sign matching the seed, with no
restriction on whether the primitive seed character is even or odd. -/
theorem seededFiniteThetaSystem_exists_with_fullSupportInterpolation_anyParity
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (P : MTT.Periods k ι f.form) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (ιp : MTT.Qbar →+* ℂ_[p]) (hpodd : p ≠ 2)
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (characters : SeededHorizontalCharacterRealizationV3 L)
    (hcharacters : characters.HasExpectedProperties)
    (scale : IntegralPeriodScale f ιp P)
    (hcomparison : ∀ s j a m, j ≤ k - 2 → m ≠ 0 →
      ι (MTT.algebraicSymbol P s j a m) * P.omega s =
        signedModularSymbol f.form s j a m) :
    ∃ Θ : SeededFiniteThetaDataV3 L,
      Θ.characters = characters ∧
      Θ.SatisfiesNormRelations ∧
      Θ.HasFullSupportCriticalZeroSetV2 := by
  obtain ⟨s, hs⟩ := exists_matchingSign η (k / 2 - 1)
  obtain ⟨Θ, hΘcharacters, hΘ⟩ := seededInverseThetaSystem_exists_forSign
    hN hk heven f hnew P η hηprim ιp hpodd L characters scale s
  have hnorm := AnyParityNorms.normRelations
    hN hk heven f P η hηprim ιp L scale Θ s hΘ
  refine ⟨Θ, hΘcharacters, hnorm, ?_⟩
  intro χ hfull
  have hexpected : Θ.characters.HasExpectedProperties := by
    rw [hΘcharacters]
    exact hcharacters
  have hatLevel := fullSupport_atLevel_apply_eq_realized_v2 Θ.characters χ hfull
  have hψeven := realizedHorizontalCharacter_even_of_odd_prime_v2
    Θ.characters hexpected hpodd χ
  let θ := primitiveProductV2 η (Θ.characters.realized χ)
  let : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
  have hθsign : (MTT.sign s : MTT.Qbar) * (-1 : MTT.Qbar) ^ (k / 2 - 1) =
      θ.2 (-1) := by
    rw [show θ.2 (-1) = η.2 (-1) from
      primitiveProductV2_apply_neg_one_of_even η (Θ.characters.realized χ) hψeven]
    exact hs
  have heval := AnyParityEvaluation.eval_ne_zero_iff
    hk heven f P η hηprim ιp L scale Θ s hΘ χ hfull hatLevel
  rw [heval]
  have hsymbol := matchingSign_algebraicSymbol_sum_ne_zero_iff_modularSymbol_sum
    hk f P θ s hθsign hcomparison
  have hθprim : θ.2.IsPrimitive := primitiveProductArithmetic_v2.primitive _ _
  have hj : k / 2 - 1 ≤ k - 2 := by omega
  exact hsymbol.trans (MTT.criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero
    hN hk ι f θ.2 hθprim (k / 2 - 1) hj).symm

/-- Normalization preserves interpolation for either seed parity. -/
theorem seededNormalizedThetaMeasure_exists_with_interpolation_anyParity
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (P : MTT.Periods k ι f.form) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (ιp : MTT.Qbar →+* ℂ_[p]) (hpodd : p ≠ 2)
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (characters : SeededHorizontalCharacterRealizationV3 L)
    (hcharacters : characters.HasExpectedProperties)
    (scale : IntegralPeriodScale f ιp P)
    (hcomparison : ∀ s j a m, j ≤ k - 2 → m ≠ 0 →
      ι (MTT.algebraicSymbol P s j a m) * P.omega s =
        signedModularSymbol f.form s j a m) :
    ∃ μ : SeededNormalizedThetaMeasureV3 L,
      μ.characters = characters ∧
      μ.InterpolatesSeededCriticalValues ∧
      (μ.measure.eval (trivialHorizontalCharacterV2 p L.exponent) ≠ 0 ↔
        @MTT.criticalLValue ι f.form
          η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0) := by
  obtain ⟨Θ, hΘcharacters, hΘnorm, hΘfull⟩ :=
    seededFiniteThetaSystem_exists_with_fullSupportInterpolation_anyParity
      hN hk heven f hnew P η hηprim ιp hpodd L characters
        hcharacters scale hcomparison
  have hΘexpected : Θ.characters.HasExpectedProperties := by
    rw [hΘcharacters]
    exact hcharacters
  have hΘunit : Θ.HasUnitEulerFactors := seededEulerFactors_areUnits_v4 f hnew η ιp L Θ
  have hΘzero := fullSupportCriticalZeroSet_descends_inverseSeed_v3
    Θ hΘexpected hΘnorm hΘunit hΘfull
  obtain ⟨μ, hμΘ, hμinterp⟩ :=
    unitNormRelationThetaSystem_to_normalizedMeasure_inverseSeed_v2 Θ hΘnorm hΘunit hΘzero
  have hμcharacters : μ.characters = characters := hμΘ.trans hΘcharacters
  exact ⟨μ, hμcharacters, hμinterp,
    seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2
      hηprim characters hcharacters μ hμcharacters hμinterp⟩

/-- Either parity of a primitive nonzero seed gives a faithful odd-prime
horizontal measure, using the corresponding signed modular symbols. -/
theorem seededHorizontalPadicLFunction_exists_of_primeSystem_anyParity
    {N k p B : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hnew : IsNewEigenform f) (P : MTT.Periods k ι f.form)
    (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (ιp : MTT.Qbar →+* ℂ_[p]) (hpodd : p ≠ 2)
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B)
    (hseedNonzero :
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0) :
    ∃ ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η,
      ν.primes = L ∧
      ν.InterpolatesSeededCriticalValuesV4 ∧
      ν.measure.eval (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0 := by
  let D := L.toConstructionData
  obtain ⟨characters, hcharacters⟩ := seededHorizontalCharacterRealization_exists_v4 D
  obtain ⟨scale⟩ := eigenform_period_lattice_uniformly_integral_v2 f hnew ιp P
  have hcomparison : ∀ s j a m, j ≤ k - 2 → m ≠ 0 →
      ι (MTT.algebraicSymbol P s j a m) * P.omega s =
        signedModularSymbol f.form s j a m := by
    intro s j a m hj hm
    exact algebraicSymbol_eq_signedModularSymbol_v3 hN hk f P s j a m hj hm
  obtain ⟨μ, hμcharacters, hinterp, htrivial⟩ :=
    seededNormalizedThetaMeasure_exists_with_interpolation_anyParity
      hN hk heven f hnew P η hηprim ιp hpodd D characters
      hcharacters scale hcomparison
  have hμproperties : μ.characters.HasExpectedProperties := by
    rw [hμcharacters]
    exact hcharacters
  exact seededHorizontalPadicLFunction_assemble_v4 f hnew η ιp L μ
    hμproperties hinterp (htrivial.mpr hseedNonzero)

end HorizontalPadicL

end BundleSeededThetaAnyParity

-- From Solutions/AnyParityPrimeSystem.lean
section BundleAnyParityPrimeSystem

/- Adapted from David Loeffler's Prove2Me submission
3810e639-fbf4-4220-98db-aec1ba0f2beb: remove the unused seed-parity hypothesis. -/

set_option autoImplicit false

open HorizontalPadicL

theorem HorizontalPadicL.seededPositiveDensityPrimeSystem_exists_anyParity
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive)
    (m B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor) :
    ∃ (ιp : MTT.Qbar →+* ℂ_[p])
      (L : SeededHorizontalPrimeSystemV3 p ιp f η B),
      L.orderExponent = m := by
  rcases seededEigenform_padicPlace_exists_v2 (p := p) hN hk ι f hnew η with ⟨V⟩
  rcases newEigenform_residualRepresentation_exists_v2 hN hk ι f hnew η V with ⟨R⟩
  rcases seedCyclotomicGaloisCharacters_exist_v4 hN η hηprim m hm hηorder
      horderCoprime hηcoprime with ⟨C⟩
  rcases disjointRamification_seededFrobeniusClass_exists_v4 hN hk heven ι f η
      m B hB hηcoprime V R C with ⟨D⟩
  rcases seededFrobeniusClass_positiveDensity_v2 D with ⟨δ, hδ, hdensity⟩
  have horderly := seededFrobeniusClass_isOrderly_inverseSeed_v2 D hηorder horderCoprime
  rcases positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2 hm D δ hδ hdensity horderly with
    ⟨L, hL⟩
  exact ⟨V.embedding, L, hL⟩

end BundleAnyParityPrimeSystem

-- From Solutions/ArbitraryParityIteration.lean
/-
Adapted from the accepted Prove2Me proof by cbirkbeck of
`HorizontalPadicL.primePowerPropagation_iterate`, submission
https://prove2.me/submissions/effa28e6-7c80-4a74-a866-17c73b5f6b26 .
The iteration and counting argument are unchanged. The seed invariant drops
its parity clause, and the propagation input quantifies over all seed parities.
-/

set_option autoImplicit false
noncomputable section BundleArbitraryParityIteration
open scoped BigOperators


namespace HorizontalPadicL

/-- Prime-power propagation with no parity restriction on the seed. The new
odd-order characters remain even, as in `seededPrimePowerTwists`. -/
def HasPrimePowerPropagationAnyParity {N k : ℕ} (ι : MTT.Qbar →+* ℂ)
    (f : MTT.Eigenform N k ι) : Prop :=
  ∀ (η : DirichletCharacterWithLevel), η.2.IsPrimitive →
    ∀ (p m B : ℕ) [Fact p.Prime], p ≠ 2 → 0 < m → 0 < B →
      2 ≤ orderOf η.2 → Nat.Coprime (orderOf η.2) p →
      Nat.Coprime (N * p) η.2.conductor →
      @MTT.criticalLValue ι f.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2
        (k / 2 - 1) ≠ 0 →
      ∃ α : ℝ, 0 < α ∧
        HasLogPowerLowerBound (seededPrimePowerNonvanishingCount ι f η p m B) α

end HorizontalPadicL

namespace HorizontalPadicL.PrimePowerIterateAnyParity

open HorizontalPadicL

/-- A positive logarithmic lower bound forces the counted set to be nonempty. -/
lemma nonempty_of_hasLogPowerLowerBound {S : Set DirichletCharacterWithLevel} {α : ℝ}
    (h : HasLogPowerLowerBound (characterConductorCount S) α) : S.Nonempty := by
  obtain ⟨c, X₀, hc, hX₀, hb⟩ := h
  set X := max X₀ 2 with hXdef
  have hX2 : (2 : ℝ) ≤ X := le_max_right _ _
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hpos : 0 < c * X / Real.log X ^ (1 - α) :=
    div_pos (mul_pos hc (by linarith)) (Real.rpow_pos_of_pos hlog _)
  have hcount := lt_of_lt_of_le hpos (hb X (le_max_left _ _))
  have hne : characterConductorCount S X ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hcount
    exact lt_irrefl _ hcount
  obtain ⟨χ, hχ, -⟩ := Set.nonempty_of_ncard_ne_zero hne
  exact ⟨χ, hχ⟩

/-- A logarithmic lower bound transfers along `g X ≤ h (C * X)` with `C ≥ 1`,
at the cost of capping the exponent at `1`. -/
lemma hasLogPowerLowerBound_of_le_scale {g h : ℝ → ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hgh : ∀ X, g X ≤ h (C * X)) {α : ℝ} (hg : HasLogPowerLowerBound g α) :
    HasLogPowerLowerBound h (min α 1) := by
  obtain ⟨c, X₀, hc, hX₀, hb⟩ := hg
  have hC0 : 0 < C := by linarith
  have hM1 : 1 ≤ max X₀ (Real.exp 1) := le_trans hX₀ (le_max_left _ _)
  refine ⟨c / C, C * max X₀ (Real.exp 1), div_pos hc hC0,
    one_le_mul_of_one_le_of_one_le hC hM1, ?_⟩
  intro Y hY
  set X := Y / C with hXdef
  have hXge : max X₀ (Real.exp 1) ≤ X := by
    rw [hXdef, le_div_iff₀ hC0]; linarith
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hXge
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hXge
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogX : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hYpos : 0 < Y := by
    have : X * C = Y := by rw [hXdef]; field_simp
    rw [← this]; exact mul_pos hXpos hC0
  have hXY : X ≤ Y := div_le_self hYpos.le hC
  have hlogXY : Real.log X ≤ Real.log Y := Real.log_le_log hXpos hXY
  have hβ0 : 0 ≤ 1 - min α 1 := by linarith [min_le_right α 1]
  have hβ : 1 - α ≤ 1 - min α 1 := by linarith [min_le_left α 1]
  have hpowX : 0 < Real.log X ^ (1 - α) := Real.rpow_pos_of_pos (by linarith) _
  have hpowXβ : 0 < Real.log X ^ (1 - min α 1) := Real.rpow_pos_of_pos (by linarith) _
  have hCX : C * X = Y := by rw [hXdef]; field_simp
  have h1 : c / C * Y / Real.log Y ^ (1 - min α 1) ≤
      c * X / Real.log X ^ (1 - min α 1) := by
    have hnum : c / C * Y = c * X := by rw [← hCX]; field_simp
    rw [hnum]
    exact div_le_div_of_nonneg_left (by positivity) hpowXβ
      (Real.rpow_le_rpow (by linarith) hlogXY hβ0)
  have h2 : c * X / Real.log X ^ (1 - min α 1) ≤ c * X / Real.log X ^ (1 - α) :=
    div_le_div_of_nonneg_left (by positivity) hpowX
      (Real.rpow_le_rpow_of_exponent_le hlogX hβ)
  have h3 : c * X / Real.log X ^ (1 - α) ≤ g X := hb X hXX₀
  have h4 : (g X : ℝ) ≤ h Y := by
    rw [← hCX]; exact_mod_cast hgh X
  linarith

/-- Primitive characters of bounded conductor form a finite set. -/
lemma finite_primitive_conductor_le (Y : ℝ) :
    {χ : DirichletCharacterWithLevel |
      χ.2.IsPrimitive ∧ (χ.2.conductor : ℝ) ≤ Y}.Finite := by
  have hbase : {N : {N : ℕ // 0 < N} | N.1 ≤ ⌊Y⌋₊}.Finite :=
    (Set.finite_le_nat ⌊Y⌋₊).preimage Subtype.val_injective.injOn
  have hfib : ∀ b ∈ {N : {N : ℕ // 0 < N} | N.1 ≤ ⌊Y⌋₊},
      ((Sigma.fst : DirichletCharacterWithLevel → {N : ℕ // 0 < N}) ⁻¹' {b}).Finite := by
    intro b _
    refine (Set.finite_range (Sigma.mk (β := fun N : {N : ℕ // 0 < N} =>
      DirichletCharacter MTT.Qbar N.1) b)).subset ?_
    rintro ⟨a, x⟩ hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨x, rfl⟩
  refine (hbase.preimage' hfib).subset ?_
  rintro χ ⟨hprim, hle⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hc : χ.2.conductor = χ.1.1 := hprim
  rw [← hc]
  exact Nat.le_floor hle

/-- Every Dirichlet character with positive level has positive conductor. -/
lemma conductor_pos (χ : DirichletCharacterWithLevel) : 0 < χ.2.conductor := by
  have : NeZero χ.1.1 := ⟨Nat.ne_of_gt χ.1.2⟩
  exact Nat.pos_of_ne_zero χ.2.conductor_ne_zero

section Seeds

variable {N k : ℕ} (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (d : ℕ)

/-- A seed: a primitive character of prescribed order whose conductor is prime to
`N * d` and whose twisted critical value is nonzero. -/
def IsSeed (o : ℕ) (η : DirichletCharacterWithLevel) : Prop :=
  η.2.IsPrimitive ∧ orderOf η.2 = o ∧
    Nat.Coprime (N * d) η.2.conductor ∧
    @MTT.criticalLValue ι f.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0

variable {ι f d}

/-- Multiplying a seed by a new twist avoiding `N * d * cond η` yields a seed whose order is
the product of the two orders. -/
lemma isSeed_primitiveProduct (harithmetic : PrimitiveProductArithmetic)
    {o q e : ℕ} {η : DirichletCharacterWithLevel} (hη : IsSeed ι f d o η)
    (hcop : Nat.Coprime o (q ^ e)) {ψ : DirichletCharacterWithLevel}
    (hψ : ψ ∈ seededPrimePowerTwists ι f η q e (N * d * η.2.conductor)) :
    IsSeed ι f d (o * q ^ e) (primitiveProductV2 η ψ) ∧
      (primitiveProductV2 η ψ).2.conductor = η.2.conductor * ψ.2.conductor := by
  obtain ⟨hηprim, hηord, hηcop, hηL⟩ := hη
  obtain ⟨hψprim, hψord, -, hψcop, hψL⟩ := hψ
  have hcond : Nat.Coprime η.2.conductor ψ.2.conductor :=
    Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hψcop
  have hNd : Nat.Coprime (N * d) ψ.2.conductor :=
    Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hψcop
  have hmul := harithmetic.conductor η ψ hηprim hψprim hcond
  refine ⟨⟨harithmetic.primitive η ψ, ?_, ?_, hψL⟩, hmul⟩
  · rw [harithmetic.order η ψ hηprim hψprim hcond (by rw [hηord, hψord]; exact hcop),
      hηord, hψord]
  · rw [hmul]; exact Nat.Coprime.mul_right hηcop hNd

/-- The prime-power decomposition used at each stage of the iteration. -/
lemma exists_primePower_split {n : ℕ} (hn : Odd n) (h1 : 1 < n) :
    ∃ q e n', q.Prime ∧ q ≠ 2 ∧ 0 < e ∧ n = n' * q ^ e ∧ n' < n ∧ Odd n' ∧
      Nat.Coprime (2 * n') (q ^ e) := by
  have hn0 : n ≠ 0 := by omega
  set q := n.minFac with hq
  have hqprime : q.Prime := Nat.minFac_prime (by omega)
  have hqdvd : q ∣ n := Nat.minFac_dvd n
  have hq2 : q ≠ 2 := by
    intro h2
    rw [h2] at hqdvd
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hqdvd)
  set e := n.factorization q with he
  have hepos : 0 < e := hqprime.factorization_pos_of_dvd hn0 hqdvd
  set n' := n / q ^ e with hn'
  have hsplit : q ^ e * n' = n := Nat.ordProj_mul_ordCompl_eq_self n q
  have hq1 : 2 ≤ q ^ e := le_trans hqprime.two_le
    (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hepos) q)
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · rw [h0, mul_zero] at hsplit; omega
    · exact h0
  have hlt : n' < n := by nlinarith
  have hodd : Odd n' := (Nat.odd_mul.mp (by rw [hsplit]; exact hn)).2
  have hcopq : Nat.Coprime q n' := Nat.coprime_ordCompl hqprime hn0
  have hcop2 : Nat.Coprime 2 q :=
    (Nat.coprime_primes Nat.prime_two hqprime).mpr (Ne.symm hq2)
  refine ⟨q, e, n', hqprime, hq2, hepos, by rw [← hsplit, mul_comm], hlt, hodd, ?_⟩
  exact Nat.Coprime.pow_right _ (Nat.coprime_mul_iff_left.mpr ⟨hcop2, hcopq.symm⟩)

end Seeds

end HorizontalPadicL.PrimePowerIterateAnyParity

open HorizontalPadicL HorizontalPadicL.PrimePowerIterateAnyParity in
theorem HorizontalPadicL.primePowerPropagation_iterate_anyParity
    {N k : ℕ} (hN : 0 < N) (_hk : 2 ≤ k) (_heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hpropagation : HasPrimePowerPropagationAnyParity ι f)
    (harithmetic : PrimitiveProductArithmetic)
    (d : ℕ) (hcase1 : d % 4 = 2 ∧ 6 ≤ d)
    (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive) (hηorder : orderOf η.2 = 2)
    (hηcoprime : Nat.Coprime (N * d) η.2.conductor)
    (hηnonzero : @MTT.criticalLValue ι f.form
      η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (eigenformNonvanishingCount ι f d) α := by
  have hd0 : 0 < d := by omega
  -- One propagation step from a seed of order `2 * n'` at the prime power `q ^ e`.
  have step : ∀ {n' q e : ℕ} {η' : DirichletCharacterWithLevel},
      IsSeed ι f d (2 * n') η' → 0 < n' → q.Prime → q ≠ 2 → 0 < e → q ∣ d →
      Nat.Coprime (2 * n') (q ^ e) →
      ∃ α : ℝ, 0 < α ∧ HasLogPowerLowerBound
        (seededPrimePowerNonvanishingCount ι f η' q e (N * d * η'.2.conductor)) α := by
    intro n' q e η' hseed hn' hq hq2 he hqd hcop
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨hprim, hord, hcopη, hL⟩ := hseed
    have hB : 0 < N * d * η'.2.conductor :=
      Nat.mul_pos (Nat.mul_pos hN hd0) (conductor_pos η')
    refine hpropagation η' hprim q e (N * d * η'.2.conductor) hq2 he hB
      (by rw [hord]; omega) ?_ ?_ hL
    · rw [hord]
      exact Nat.Coprime.coprime_dvd_right (dvd_pow_self q (Nat.pos_iff_ne_zero.mp he)) hcop
    · exact Nat.Coprime.coprime_dvd_left (Nat.mul_dvd_mul_left N hqd) hcopη
  -- Every odd divisor `n` of `d` admits a seed of order `2 * n`.
  have seeds : ∀ n : ℕ, Odd n → n ∣ d → ∃ η' : DirichletCharacterWithLevel,
      IsSeed ι f d (2 * n) η' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hodd hdvd
      rcases Nat.lt_or_ge 1 n with h1 | h1
      · obtain ⟨q, e, n', hq, hq2, he, hsplit, hlt, hodd', hcop⟩ :=
          exists_primePower_split hodd h1
        have hn'd : n' ∣ d := Nat.dvd_trans ⟨q ^ e, hsplit⟩ hdvd
        have hqd : q ∣ d := Nat.dvd_trans
          (Nat.dvd_trans (dvd_pow_self q (Nat.pos_iff_ne_zero.mp he)) ⟨n', by
            rw [hsplit, mul_comm]⟩) hdvd
        obtain ⟨η', hη'⟩ := ih n' hlt hodd' hn'd
        obtain ⟨α, -, hα⟩ := step hη' hodd'.pos hq hq2 he hqd hcop
        obtain ⟨ψ, hψ⟩ := nonempty_of_hasLogPowerLowerBound hα
        refine ⟨primitiveProductV2 η' ψ, ?_⟩
        have := (isSeed_primitiveProduct harithmetic hη' hcop hψ).1
        rwa [mul_assoc, ← hsplit] at this
      · have hn1 : n = 1 := by have := hodd.pos; omega
        subst hn1
        exact ⟨η, hηprim, by rw [hηorder], hηcoprime, hηnonzero⟩
  -- The last stage keeps the quantitative family.
  set n := d / 2 with hn
  have hd2 : d = 2 * n := by omega
  have hodd : Odd n := by rw [Nat.odd_iff]; omega
  have h1 : 1 < n := by omega
  obtain ⟨q, e, n', hq, hq2, he, hsplit, -, hodd', hcop⟩ := exists_primePower_split hodd h1
  have hnd : n ∣ d := ⟨2, by omega⟩
  have hn'd : n' ∣ d := Nat.dvd_trans ⟨q ^ e, hsplit⟩ hnd
  have hqd : q ∣ d := Nat.dvd_trans
    (Nat.dvd_trans (dvd_pow_self q (Nat.pos_iff_ne_zero.mp he)) ⟨n', by
      rw [hsplit, mul_comm]⟩) hnd
  obtain ⟨η', hη'⟩ := seeds n' hodd' hn'd
  obtain ⟨α, hα, hbound⟩ := step hη' hodd'.pos hq hq2 he hqd hcop
  have hCnat : 1 ≤ η'.2.conductor := conductor_pos η'
  refine ⟨min α 1, lt_min hα one_pos, ?_⟩
  refine hasLogPowerLowerBound_of_le_scale (C := (η'.2.conductor : ℝ))
    (by exact_mod_cast hCnat) ?_ hbound
  intro X
  unfold seededPrimePowerNonvanishingCount characterConductorCount eigenformNonvanishingCount
  refine Set.ncard_le_ncard_of_injOn (fun ψ => primitiveProductV2 η' ψ) ?_ ?_
    (((finite_primitive_conductor_le ((η'.2.conductor : ℝ) * X))).subset ?_)
  · rintro ψ ⟨hψ, hψX⟩
    obtain ⟨⟨hprim, hord, hcopθ, hL⟩, hcondθ⟩ :=
      isSeed_primitiveProduct harithmetic hη' hcop hψ
    refine ⟨hprim, ?_, ?_, ?_, hL⟩
    · rw [hord, mul_assoc, ← hsplit, ← hd2]
    · rw [hcondθ, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left hψX (Nat.cast_nonneg _)
    · have hlev : (primitiveProductV2 η' ψ).2.conductor = (primitiveProductV2 η' ψ).1.1 :=
        hprim
      rw [← hlev]
      exact Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcopθ
  · rintro ψ₁ ⟨hψ₁, -⟩ ψ₂ ⟨hψ₂, -⟩ heq
    have hcond : ∀ ψ ∈ seededPrimePowerTwists ι f η' q e (N * d * η'.2.conductor),
        ψ.2.IsPrimitive ∧ Nat.Coprime η'.2.conductor ψ.2.conductor := fun ψ hψ =>
      ⟨hψ.1, Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hψ.2.2.2.1⟩
    have := harithmetic.injective η' hη'.1 (a₁ := ⟨ψ₁, hcond ψ₁ hψ₁⟩)
      (a₂ := ⟨ψ₂, hcond ψ₂ hψ₂⟩) heq
    exact congrArg Subtype.val this
  · rintro χ ⟨hprim, -, hle, -⟩
    exact ⟨hprim, hle⟩

end BundleArbitraryParityIteration

-- From Solutions/AnyParityPropagation.lean
set_option autoImplicit false
noncomputable section BundleAnyParityPropagation

namespace HorizontalPadicL

/-- Uniform seeded horizontal construction at odd primes, allowing either
parity for the primitive seed. The existing V4 interpolation and inverse-seed
Euler convention are retained. -/
def HasSeededHorizontalPadicLConstructionAnyParity
    {N k : ℕ} (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) : Prop :=
  ∀ (η : DirichletCharacterWithLevel)
    (_hηprim : η.2.IsPrimitive)
    (p m B : ℕ) [Fact p.Prime]
    (_hpodd : p ≠ 2)
    (_hm : 0 < m) (_hB : 0 < B)
    (_hηorder : 2 ≤ orderOf η.2)
    (_horderCoprime : Nat.Coprime (orderOf η.2) p)
    (_hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (_hseedNonzero :
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0),
    ∃ (ιp : MTT.Qbar →+* ℂ_[p])
      (ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η),
      ν.primes.orderExponent = m ∧
      ν.InterpolatesSeededCriticalValuesV4 ∧
      ν.measure.eval (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0

/-- The existing single-measure propagation theorem already permits either
seed parity. Only the uniform construction hypothesis needs strengthening. -/
theorem seededHorizontalConstruction_primePowerPropagation_anyParity
    {N k : ℕ} (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hconstruction : HasSeededHorizontalPadicLConstructionAnyParity ι f) :
    HasPrimePowerPropagationAnyParity ι f := by
  intro η hηprim p m B hp hpodd hm hB hηorder horder hcoprime hnonzero
  obtain ⟨ιp, ν, hexponent, hinterp, htriv⟩ :=
    hconstruction η hηprim p m B hpodd hm hB hηorder horder hcoprime hnonzero
  exact ν.primePower_propagation_v2 hpodd m hm hexponent hinterp htriv

/-- An arbitrary-parity nonzero quadratic seed and uniform seeded construction
imply the logarithmic lower bound for exact-order-d nonvanishing twists. -/
theorem seededHorizontalPadicLConstruction_implies_corollary_5_17_anyParity
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hconstruction : HasSeededHorizontalPadicLConstructionAnyParity ι f)
    (d : ℕ) (hcase1 : d % 4 = 2 ∧ 6 ≤ d)
    (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive) (hηorder : orderOf η.2 = 2)
    (hηcoprime : Nat.Coprime (N * d) η.2.conductor)
    (hηnonzero : @MTT.criticalLValue ι f.form
      η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (eigenformNonvanishingCount ι f d) α :=
  primePowerPropagation_iterate_anyParity hN hk heven ι f
    (seededHorizontalConstruction_primePowerPropagation_anyParity ι f hconstruction)
    primitiveProductArithmetic_v2 d hcase1 η hηprim hηorder hηcoprime hηnonzero

end HorizontalPadicL

end BundleAnyParityPropagation

-- From Solutions/AnyParityConstruction.lean
section BundleAnyParityConstruction

set_option autoImplicit false

namespace HorizontalPadicL

/-- Construct the seeded horizontal measure using the sign matching the seed. -/
theorem eigenform_seededHorizontalPadicLConstruction_anyParity
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hnew : IsNewEigenform f) :
    HasSeededHorizontalPadicLConstructionAnyParity ι f := by
  obtain ⟨P⟩ := MTT.periods_exist hN hk ι f
  intro η hηprim p m B _ hpodd hm hB hηorder horderCoprime hηcoprime hseedNonzero
  obtain ⟨ιp, L, hLm⟩ := seededPositiveDensityPrimeSystem_exists_anyParity
    hN hk heven ι f hnew η hηprim m B hm hB hηorder horderCoprime hηcoprime
  obtain ⟨ν, hνL, hνinterp, hνzero⟩ :=
    seededHorizontalPadicLFunction_exists_of_primeSystem_anyParity
      hN hk heven ι f hnew P η hηprim ιp hpodd L hseedNonzero
  refine ⟨ιp, ν, ?_, hνinterp, hνzero⟩
  rw [hνL]
  exact hLm

end HorizontalPadicL

end BundleAnyParityConstruction

-- From Solutions/AnyParityCorollary.lean
section BundleAnyParityCorollary

set_option autoImplicit false

open HorizontalPadicL

/-- Corollary 5.17 via a quadratic seed of either parity. -/
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (d : ℕ) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (eigenformNonvanishingCount ι f d) α := by
  obtain ⟨η, hηprim, hηorder, hηcoprime, hηnonzero⟩ :=
    friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2
      hN hk heven ι f d (by omega)
  exact seededHorizontalPadicLConstruction_implies_corollary_5_17_anyParity
    hN hk heven ι f (eigenform_seededHorizontalPadicLConstruction_anyParity hN hk heven ι f hnew)
    d hcase1 η hηprim hηorder hηcoprime hηnonzero

end BundleAnyParityCorollary
