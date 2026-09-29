-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5fce1420-8545-507b-a337-2751913454ee

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent
open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel

set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace Ws23NormOneFibreIdeleAt

variable (K : Type) [Field K] [NumberField K]

private noncomputable def placed (w : HeightOneSpectrum (𝓞 K)) (t : (w.adicCompletion K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K w t)

private theorem placed_val_fst (w : HeightOneSpectrum (𝓞 K)) (t : (w.adicCompletion K)ˣ) :
    ((placed K w t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 :=
  finIncl_apply_fst (𝓞 K) K _

private theorem placed_val_snd (w : HeightOneSpectrum (𝓞 K)) (t : (w.adicCompletion K)ˣ) :
    ((placed K w t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      = ((localUnit (𝓞 K) K w t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) :=
  finIncl_apply_snd (𝓞 K) K _

private theorem placed_apply_self (w : HeightOneSpectrum (𝓞 K)) (t : (w.adicCompletion K)ˣ) :
    (((placed K w t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = t := by
  rw [placed_val_snd]
  exact localUnit_apply_self (𝓞 K) K w t

private theorem placed_apply_of_ne
    (w : HeightOneSpectrum (𝓞 K)) (t : (w.adicCompletion K)ˣ) {w' : HeightOneSpectrum (𝓞 K)}
    (h : w' ≠ w) :
    (((placed K w t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w' = 1 := by
  rw [placed_val_snd]
  exact localUnit_apply_of_ne (𝓞 K) K w t h

private theorem val_idelicNorm (u : (AdeleRing (𝓞 K) K)ˣ) :
    (((genuineBaseChange ℚ K).idelicNorm u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)
      = (letI := (M4aHerbrand.Bridge.genuineβ ℚ K).toAlgebra;
          Algebra.norm (AdeleRing (𝓞 ℚ) ℚ) (u : AdeleRing (𝓞 K) K)) :=
  rfl

private theorem idelicNorm_eq_one (u : (AdeleRing (𝓞 K) K)ˣ) (h1 : (u : AdeleRing (𝓞 K) K).1 = 1)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      letI := Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) v;
      ∏ w : v.Extension (𝓞 K),
        Algebra.norm (v.adicCompletion ℚ) (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w.1) = 1) :
    (genuineBaseChange ℚ K).idelicNorm u = 1 := by
  apply Units.ext
  rw [Units.val_one, val_idelicNorm]
  obtain ⟨hA, hF⟩ := M4aHerbrand.genuineAdelicNorm_componentwise ℚ K (u : AdeleRing (𝓞 K) K)
  refine Prod.ext ?_ ?_
  · rw [hA, h1]
    exact map_one _
  · ext v
    rw [hF v, h2 v]
    rfl

section Members

variable {K}

private noncomputable abbrev localDeg (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : p₀.Extension (𝓞 K)) : ℕ :=
  Module.finrank (p₀.adicCompletion ℚ) (w.1.adicCompletion K)

private noncomputable def liftUnit
    (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : p₀.Extension (𝓞 K)) (x : (p₀.adicCompletion ℚ)ˣ) :
    (w.1.adicCompletion K)ˣ :=
  Units.map (algebraMap (p₀.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom x

private theorem localDeg_ne_zero (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : p₀.Extension (𝓞 K)) : localDeg p₀ w ≠ 0 :=
  Module.finrank_pos.ne'

private theorem liftUnit_val (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : p₀.Extension (𝓞 K)) (x : (p₀.adicCompletion ℚ)ˣ) :
    ((liftUnit p₀ w x : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K)
      = algebraMap (p₀.adicCompletion ℚ) (w.1.adicCompletion K) x :=
  rfl

private theorem norm_liftUnit (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : p₀.Extension (𝓞 K)) (x : (p₀.adicCompletion ℚ)ˣ) :
    Algebra.norm (p₀.adicCompletion ℚ) ((liftUnit p₀ w x : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K)
      = (x : p₀.adicCompletion ℚ) ^ localDeg p₀ w := by
  simp [liftUnit, Algebra.norm_algebraMap]

private theorem valued_liftUnit (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : p₀.Extension (𝓞 K)) (x : (p₀.adicCompletion ℚ)ˣ)
    (hx : Valued.v (x : p₀.adicCompletion ℚ) = 1) :
    Valued.v ((liftUnit p₀ w x : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K) = 1 := by
  rw [liftUnit_val]
  change Valued.v (w.adicCompletionSemialgHom ℚ K (x : p₀.adicCompletion ℚ)) = 1
  rw [w.valued_adicCompletionSemialgHom ℚ K, hx, one_pow]

private theorem liftUnit_ne_one (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : p₀.Extension (𝓞 K)) {x : (p₀.adicCompletion ℚ)ˣ}
    (hx : x ≠ 1) : ((liftUnit p₀ w x : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K) ≠ 1 := by
  rw [liftUnit_val]
  intro h
  apply hx
  apply Units.ext
  exact (algebraMap (p₀.adicCompletion ℚ) (w.1.adicCompletion K)).injective (h.trans (map_one _).symm)

end Members

namespace InfiniteOrderUnit

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

private theorem exists_valued_eq_one_pow_ne_one [CharZero F] (v : HeightOneSpectrum R) {n : ℕ} (hn : n ≠ 0)
    (hmem : (n : R) ∈ v.asIdeal) :
    ∃ x : (v.adicCompletion F)ˣ, Valued.v (x : v.adicCompletion F) = 1 ∧ ∀ m : ℕ, m ≠ 0 → x ^ m ≠ 1 := by
  have h1n : ((1 + n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hval : v.valuation F ((1 + n : ℕ) : F) = 1 := by
    have hn' : v.valuation F (n : F) < 1 := by
      have : (n : F) = algebraMap R F (n : R) := by simp
      rw [this, valuation_of_algebraMap]
      exact (v.intValuation_lt_one_iff_mem (n : R)).mpr hmem
    rw [Nat.cast_add, Nat.cast_one]
    have h := Valuation.map_add_eq_of_lt_left (v.valuation F) (x := (1 : F)) (y := (n : F)) (by simpa using hn')
    simpa using h
  set a : F := ((1 + n : ℕ) : F) with ha
  set x₀ : v.adicCompletion F := algebraMap F (v.adicCompletion F) a with hx₀
  have hvx : Valued.v x₀ = 1 := by
    rw [hx₀, algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
      valuedAdicCompletion_eq_valuation']
    exact hval
  have hx0 : x₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact zero_ne_one hvx
  refine ⟨Units.mk0 x₀ hx0, hvx, ?_⟩
  intro m hm hpow
  have h : x₀ ^ m = 1 := by
    have := congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hpow
    simpa using this
  rw [hx₀, ← map_pow, ← (algebraMap F (v.adicCompletion F)).map_one] at h
  have h' : a ^ m = 1 := (algebraMap F (v.adicCompletion F)).injective h
  rw [ha, ← Nat.cast_pow, Nat.cast_eq_one] at h'
  rcases Nat.pow_eq_one.mp h' with h2 | h2 <;> omega

end InfiniteOrderUnit

section Assembly

variable {K}

private theorem exists_unit (p₀ : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : (p₀.adicCompletion ℚ)ˣ, Valued.v (x : p₀.adicCompletion ℚ) = 1 ∧ ∀ m : ℕ, m ≠ 0 → x ^ m ≠ 1 :=
  InfiniteOrderUnit.exists_valued_eq_one_pow_ne_one p₀
    ((Ideal.absNorm_eq_zero_iff.not.mpr p₀.ne_bot)) (Ideal.absNorm_mem p₀.asIdeal)

private theorem apply_mul (a b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w
      = ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w
        * ((b : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w :=
  rfl

private theorem spec_of_two (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w₁ w₂ : p₀.Extension (𝓞 K)) (hw : w₁.1 ≠ w₂.1)
    (t₁ : (w₁.1.adicCompletion K)ˣ) (t₂ : (w₂.1.adicCompletion K)ˣ)
    (h₁ : Valued.v (t₁ : w₁.1.adicCompletion K) = 1) (h₂ : Valued.v (t₂ : w₂.1.adicCompletion K) = 1)
    (hnorm : Algebra.norm (p₀.adicCompletion ℚ) (t₁ : w₁.1.adicCompletion K)
      * Algebra.norm (p₀.adicCompletion ℚ) (t₂ : w₂.1.adicCompletion K) = 1)
    (hne : (t₁ : w₁.1.adicCompletion K) ≠ 1) :
    ∃ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 ∧
      (∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 ℚ) ≠ p₀ →
        ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1) ∧
      (∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1) ∧
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w₁.1 ≠ 1 ∧
      (genuineBaseChange ℚ K).idelicNorm u = 1 := by
  refine ⟨placed K w₁.1 t₁ * placed K w₂.1 t₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]
    exact (Prod.fst_mul _ _).trans (by rw [placed_val_fst, placed_val_fst, mul_one])
  · intro w hw'
    have hw₁ : w ≠ w₁.1 := fun h => hw' (h ▸ w₁.2)
    have hw₂ : w ≠ w₂.1 := fun h => hw' (h ▸ w₂.2)
    rw [apply_mul, placed_apply_of_ne K _ _ hw₁, placed_apply_of_ne K _ _ hw₂, mul_one]
  · intro w
    rw [apply_mul, Valuation.map_mul]
    by_cases e₁ : w = w₁.1
    · subst e₁
      rw [placed_apply_self, placed_apply_of_ne K _ _ hw, h₁, Valuation.map_one, mul_one]
    · rw [placed_apply_of_ne K _ _ e₁, Valuation.map_one, one_mul]
      by_cases e₂ : w = w₂.1
      · subst e₂; rw [placed_apply_self, h₂]
      · rw [placed_apply_of_ne K _ _ e₂, Valuation.map_one]
  · rw [apply_mul, placed_apply_self, placed_apply_of_ne K _ _ hw, mul_one]
    exact hne
  · apply idelicNorm_eq_one
    · rw [Units.val_mul]
      exact (Prod.fst_mul _ _).trans (by rw [placed_val_fst, placed_val_fst, mul_one])
    · intro v
      by_cases hv : v = p₀
      · subst hv
        letI := Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) v
        refine (Fintype.prod_eq_mul w₁ w₂ (fun h => hw (congrArg Subtype.val h)) ?_).trans ?_
        · intro c hc
          have hc₁ : c.1 ≠ w₁.1 := fun h => hc.1 (Subtype.ext h)
          have hc₂ : c.1 ≠ w₂.1 := fun h => hc.2 (Subtype.ext h)
          rw [apply_mul, placed_apply_of_ne K _ _ hc₁, placed_apply_of_ne K _ _ hc₂, mul_one, map_one]
        · rw [apply_mul, apply_mul, placed_apply_self, placed_apply_of_ne K _ _ hw,
            placed_apply_of_ne K _ _ (Ne.symm hw), placed_apply_self, mul_one, one_mul]
          exact hnorm
      · letI := Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) v
        apply Finset.prod_eq_one
        intro c _
        have hc₁ : c.1 ≠ w₁.1 := fun h => hv (by rw [← c.2, h, w₁.2])
        have hc₂ : c.1 ≠ w₂.1 := fun h => hv (by rw [← c.2, h, w₂.2])
        rw [apply_mul, placed_apply_of_ne K _ _ hc₁, placed_apply_of_ne K _ _ hc₂, mul_one, map_one]

end Assembly

end Ws23NormOneFibreIdeleAt

theorem solution
    (K : Type) [Field K] [NumberField K]
    (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w₀ w₂ : p₀.Extension (𝓞 K)) (hne : w₀.1 ≠ w₂.1) :
    ∃ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 ∧
      (∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 ℚ) ≠ p₀ →
        ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1) ∧
      (∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1) ∧
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w₀.1 ≠ 1 ∧
      (genuineBaseChange ℚ K).idelicNorm u = 1 := by
  open Ws23NormOneFibreIdeleAt in
  obtain ⟨x, hx, hxord⟩ := exists_unit p₀
  have hd₂ : localDeg p₀ w₂ ≠ 0 := localDeg_ne_zero p₀ w₂
  refine spec_of_two p₀ w₀ w₂ hne (liftUnit p₀ w₀ (x ^ localDeg p₀ w₂))
    (liftUnit p₀ w₂ (x⁻¹ ^ localDeg p₀ w₀)) (valued_liftUnit p₀ w₀ _ ?_) (valued_liftUnit p₀ w₂ _ ?_) ?_
    (liftUnit_ne_one p₀ w₀ (hxord _ hd₂))
  · rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  · rw [Units.val_pow_eq_pow_val, map_pow, Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one, one_pow]
  · rw [norm_liftUnit, norm_liftUnit, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      ← pow_mul, ← pow_mul, inv_pow, mul_comm (localDeg p₀ w₀), mul_inv_cancel₀]
    exact pow_ne_zero _ x.ne_zero

end S_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne (solution)
