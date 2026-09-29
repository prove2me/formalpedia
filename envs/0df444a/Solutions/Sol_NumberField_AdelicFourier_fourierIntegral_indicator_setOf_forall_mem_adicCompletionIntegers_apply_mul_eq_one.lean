-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5c818dd6-5cb4-50d1-92f5-803f6e338853

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField NumberField.AdelicFourier IsDedekindDomain MeasureTheory

namespace Ws1
namespace F3

open NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_invUnif_pow (k : ℕ) :
    Valued.v ((((uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ k) =
      WithZero.exp (k : ℤ) := by
  rw [map_pow, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit, ← WithZero.exp_neg, neg_neg,
    ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]

end Ws1.F3

theorem solution
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : Continuous ψ)
    (h0 : ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ z = 1)
    (h1 : ∃ z : v.adicCompletion F, ψ z ≠ 1) :
    IsOpen {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} ∧
    IsCompact {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} ∧
    ∀ w : v.adicCompletion F,
      fourierIntegral ψ μ
          ({y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1}.indicator
            fun _ => (1 : ℂ)) w =
        (μ.real {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} : ℂ) *
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) w := by
  classical

  set L : Set (v.adicCompletion F) :=
    {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} with hLdef
  have hOL : ∀ y, y ∈ v.adicCompletionIntegers F → y ∈ L := fun y hy z hz => h0 _ (mul_mem hz hy)
  have hLmod : ∀ t, t ∈ v.adicCompletionIntegers F → ∀ y ∈ L, t * y ∈ L := fun t ht y hy z hz => by
    show ψ (z * (t * y)) = 1
    rw [← mul_assoc]; exact hy _ (mul_mem hz ht)
  have hLsub : ∀ y₁ ∈ L, ∀ y₂ ∈ L, y₁ - y₂ ∈ L := fun y₁ hy₁ y₂ hy₂ z hz => by
    have h := AddChar.map_add_eq_mul ψ (z * (y₁ - y₂)) (z * y₂)
    rw [← mul_add, sub_add_cancel, hy₁ z hz, hy₂ z hz, mul_one] at h
    exact h.symm
  have hLneg : ∀ y ∈ L, -y ∈ L := fun y hy => by
    have := hLsub 0 (hOL 0 (zero_mem _)) y hy
    rwa [zero_sub] at this

  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := Valued.isOpen_valuationSubring _
  have hopen : IsOpen L := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hsub : (fun y' => y' - y) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ⊆ L := by
      intro y' hy'
      have h := hLsub _ (hOL _ hy') _ (hLneg y hy)
      simpa using h
    exact Filter.mem_of_superset ((hOopen.preimage (continuous_sub_right y)).mem_nhds (by simp [zero_mem])) hsub

  obtain ⟨x, hψx⟩ := h1
  have hx0 : x ≠ 0 := by rintro rfl; exact hψx (by simp)
  have hbound : ∀ y ∈ L, Valued.v y < Valued.v x := by
    intro y hy
    by_contra hle
    rw [not_lt] at hle
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff] at hle
      exact hx0 ((Valuation.zero_iff _).mp hle)
    have hz : x / y ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    have := hy (x / y) hz
    rw [div_mul_cancel₀ x hy0] at this
    exact hψx this
  have hclosed : IsClosed L := by
    have hL : L = ⋂ z : v.adicCompletionIntegers F, (fun y => ψ ((z : v.adicCompletion F) * y)) ⁻¹' {1} := by
      ext y
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hy z => hy z z.2, fun hy z hz => hy ⟨z, hz⟩⟩
    rw [hL]
    exact isClosed_iInter fun z => isClosed_singleton.preimage (hψ.comp (continuous_const.mul continuous_id))
  have hOcompact : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  have hcompact : IsCompact L := by
    have hK : IsCompact ((fun t => x * t) '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
      hOcompact.image (continuous_const.mul continuous_id)
    refine hK.of_isClosed_subset hclosed fun y hy => ?_
    refine ⟨y / x, ?_, mul_div_cancel₀ y hx0⟩
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ (hbound y hy).le zero_le'
  refine ⟨hopen, hcompact, fun w => ?_⟩

  have hLmeas : MeasurableSet L := hopen.measurableSet
  have hint : fourierIntegral ψ μ (L.indicator fun _ => (1 : ℂ)) w = ∫ y in L, ψ (-(y * w)) ∂μ := by
    rw [fourierIntegral, ← integral_indicator hLmeas]
    congr 1 with y
    by_cases hy : y ∈ L
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [hint]
  by_cases hw : w ∈ v.adicCompletionIntegers F
  ·
    rw [Set.indicator_of_mem (SetLike.mem_coe.mpr hw), mul_one]
    have h1 : ∀ y ∈ L, ψ (-(y * w)) = 1 := fun y hy => by
      rw [show -(y * w) = (-w) * y by ring]
      exact hy _ (neg_mem hw)
    rw [setIntegral_congr_fun hLmeas h1, setIntegral_const, Complex.real_smul, mul_one]
  ·
    rw [Set.indicator_of_notMem (fun h => hw (SetLike.mem_coe.mp h)), mul_zero]

    have hw1 : WithZero.exp (1 : ℤ) ≤ Valued.v w := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hw
      have hw0 : Valued.v w ≠ 0 := (lt_trans zero_lt_one hw).ne'
      rw [← WithZero.exp_log hw0] at hw ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hw
      rw [WithZero.exp_le_exp]
      omega
    set π : v.adicCompletion F := (((NumberField.AdelicLevel.uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) with hπ
    have hπk : ∀ k : ℕ, Valued.v (π ^ k) = WithZero.exp (k : ℤ) := Ws1.F3.valued_invUnif_pow F v

    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k : ℕ, π ^ k ∈ L → k ≤ N := by
      obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
        ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx0)).symm⟩
      refine ⟨m.toNat, fun k hk => ?_⟩
      have h := hbound _ hk
      rw [hπk, hm, WithZero.exp_lt_exp] at h
      omega
    set k₀ : ℕ := Nat.findGreatest (fun k => π ^ k ∈ L) N with hk₀
    have hk₀mem : π ^ k₀ ∈ L := by
      exact Nat.findGreatest_spec (P := fun k => π ^ k ∈ L) (Nat.zero_le N) (by show π ^ 0 ∈ L; rw [pow_zero]; exact hOL 1 (one_mem _))
    have hk₀max : π ^ (k₀ + 1) ∉ L := fun h =>
      Nat.findGreatest_is_greatest (P := fun k => π ^ k ∈ L) (Nat.lt_succ_self k₀) (hN _ h) h

    have hnot : ¬ ∀ y ∈ L, ψ (-(y * w)) = 1 := by
      intro hall
      have hmem : π ^ k₀ * w ∈ L := by
        intro z hz
        have h := hall (-(z * π ^ k₀)) (hLneg _ (hLmod z hz _ hk₀mem))
        rw [show -(-(z * π ^ k₀) * w) = z * (π ^ k₀ * w) by ring] at h
        exact h
      have hw0 : w ≠ 0 := by
        rintro rfl
        rw [map_zero] at hw1
        exact WithZero.exp_ne_zero (le_zero_iff.mp hw1)
      have ht : π / w ∈ v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        have hπ1 : Valued.v π = WithZero.exp 1 := by have := hπk 1; rwa [pow_one, Nat.cast_one] at this
        rw [hπ1]
        exact div_le_one_of_le₀ hw1 zero_le'
      have hnext : π ^ (k₀ + 1) ∈ L := by
        have h := hLmod _ ht _ hmem
        rw [show π / w * (π ^ k₀ * w) = π ^ (k₀ + 1) by rw [pow_succ]; field_simp] at h
        exact h
      exact hk₀max hnext
    push Not at hnot
    obtain ⟨y₀, hy₀L, hy₀⟩ := hnot

    set I : ℂ := ∫ y in L, ψ (-(y * w)) ∂μ with hI
    have htrans : I = ψ (-(y₀ * w)) * I := by
      rw [hI, ← integral_indicator hLmeas]
      conv_lhs => rw [← integral_add_right_eq_self (fun y => L.indicator (fun y => ψ (-(y * w))) y) y₀]
      rw [← integral_const_mul]
      congr 1 with y
      by_cases hy : y ∈ L
      · have hy' : y + y₀ ∈ L := by
          have := hLsub _ hy _ (hLneg _ hy₀L); rwa [sub_neg_eq_add] at this
        rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy, ← AddChar.map_add_eq_mul]
        congr 1; ring
      · have hy' : y + y₀ ∉ L := fun h => hy (by have := hLsub _ h _ hy₀L; rwa [add_sub_cancel_right] at this)
        rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy, mul_zero]
    have h1ne : (1 : ℂ) - ψ (-(y₀ * w)) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hy₀
      exact h.symm
    have hzero : (1 - ψ (-(y₀ * w))) * I = 0 := by rw [sub_mul, one_mul, ← htrans, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left h1ne

end S_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one (solution)
