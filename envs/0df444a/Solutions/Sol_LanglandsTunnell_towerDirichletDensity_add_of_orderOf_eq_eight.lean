-- Prove2me | solution 1 for LanglandsTunnell.towerDirichletDensity_add_of_orderOf_eq_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/08850322-47d4-504e-82ff-81e2960226e2

import Definitions.Def_LanglandsTunnell_AnalyticGates
import Definitions.Def_FrobeniusDensity_BadPrimes
import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Theorems.Thm_FrobeniusDensity_weight_eq
import Theorems.Thm_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed
import Theorems.Thm_FrobeniusDensity_degOneAsymptotic
import Theorems.Thm_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight
import Theorems.Thm_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer
import Theorems.Thm_FrobeniusDensity_sum_moebius_mul_eq_totient
import Mathlib.RingTheory.Frobenius
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_towerDirichletDensity_add_of_orderOf_eq_eight
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow"

set_option autoImplicit false

p2m_open "Filter Topology Asymptotics NumberField Ideal NumberField.Ideal FrobeniusDensity"

namespace FltWs24
namespace DivisionDensity

open LanglandsTunnell

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

open scoped Classical in

theorem classIndicator_eq_ite (σ : L ≃ₐ[ℚ] L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hbad : ℓ ∉ badPrimes L)
    (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime] [Q₀.LiesOver (ratPrimeIdeal ℓ)] :
    haveI : Finite ((𝓞 L) ⧸ Q₀) :=
      finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    classIndicator σ ℓ = if IsConj σ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀) then 1 else 0 := by
  classical
  haveI : Finite ((𝓞 L) ⧸ Q₀) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  unfold classIndicator
  by_cases hc : IsConj σ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀)
  · rw [if_pos hc, if_pos]
    exact ⟨hℓ, Q₀, inferInstance, inferInstance,
      inertia_eq_bot_of_notMem_badPrimes L hℓ hbad Q₀, hc⟩
  · rw [if_neg hc, if_neg]
    rintro ⟨_, Q, hQp, hQl, _, hQc⟩
    haveI := hQp; haveI := hQl
    exact hc (hQc.trans (isConj_arithFrobAt_of_liesOver hℓ Q Q₀))

theorem classIndicator_of_not_prime (σ : L ≃ₐ[ℚ] L) {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) :
    classIndicator σ ℓ = 0 := by
  classical
  unfold classIndicator
  rw [if_neg]
  rintro ⟨h, _⟩
  exact hℓ h

theorem classIndicator_mul_rpow_le (σ : L ≃ₐ[ℚ] L) (s : ℝ) (ℓ : ℕ) :
    (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s) ≤ (ℓ : ℝ) ^ (-s) := by
  have h1 : (classIndicator σ ℓ : ℝ) ≤ 1 := by exact_mod_cast classIndicator_le_one σ ℓ
  have h2 : 0 ≤ (ℓ : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg ℓ) _
  nlinarith

theorem classIndicator_mul_rpow_nonneg (σ : L ≃ₐ[ℚ] L) (s : ℝ) (ℓ : ℕ) :
    0 ≤ (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s) :=
  mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg ℓ) _)

theorem summable_classIndicator (σ : L ≃ₐ[ℚ] L) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s)) := by
  have hsum : Summable (fun ℓ : ℕ => (ℓ : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  exact hsum.of_nonneg_of_le (classIndicator_mul_rpow_nonneg σ s) (classIndicator_mul_rpow_le σ s)

theorem badPiece_le (σ : L ≃ₐ[ℚ] L) (S₀ : Finset ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |∑ ℓ ∈ S₀, (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s)| ≤ S₀.card := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun ℓ _ => classIndicator_mul_rpow_nonneg σ s ℓ)]
  have : ∀ ℓ ∈ S₀, (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s) ≤ 1 := by
    intro ℓ _
    refine (classIndicator_mul_rpow_le σ s ℓ).trans ?_
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0
      rcases eq_or_ne s 0 with rfl | hs0
      · simp
      · rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hs0)]; exact zero_le_one
    · have h1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hpos
      exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  calc ∑ ℓ ∈ S₀, (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s)
      ≤ ∑ _ℓ ∈ S₀, (1 : ℝ) := Finset.sum_le_sum this
    _ = S₀.card := by simp

theorem ind_nonneg (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : 0 ≤ ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) :=
  add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ind_le_two (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) ≤ 2 := by
  have h1 : (classIndicator σ ℓ : ℝ) ≤ 1 := Nat.cast_le_one.mpr (classIndicator_le_one σ ℓ)
  have h2 : (classIndicator (σ ^ 5) ℓ : ℝ) ≤ 1 := Nat.cast_le_one.mpr (classIndicator_le_one (σ ^ 5) ℓ)
  linarith

theorem towerDirichletDensity_add_of_orderOf_eq_eight (σ : L ≃ₐ[ℚ] L)
    (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ =>
        (∑' ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + (2 * (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) / (Nat.card (L ≃ₐ[ℚ] L) : ℝ))
        * Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  classical
  refine ⟨fun s hs => summable_classIndicator σ hs, ?_⟩
  have hL := degOneAsymptotic L
  set S₀ : Finset ℕ := badPrimes L with hS₀
  have h8' : orderOf σ = 8 := h8
  set n : ℕ := orderOf σ with hn
  have hn0 : 0 < n := orderOf_pos σ
  set E : ℕ → IntermediateField ℚ L := fun f =>
    FixedPoints.intermediateField (Subgroup.zpowers (σ ^ (orderOf σ / f))) with hE

  set M : ℤ := ∑ f ∈ (orderOf σ).divisors,
    (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) with hM
  have hMφ : M = (n.totient : ℤ) := sum_moebius_mul_eq_totient n hn0
  have hM4 : M = 4 := by rw [hMφ, h8]; decide
  set cz : ℕ := Nat.card (Subgroup.centralizer ({σ} : Set (L ≃ₐ[ℚ] L))) with hcz
  have hcz0 : 0 < cz := Nat.card_pos
  set κ : ℝ := 2 * (cz : ℝ) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; exact mul_pos two_pos (by exact_mod_cast hcz0)
  have hind_nonneg : ∀ ℓ : ℕ, 0 ≤ ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) := ind_nonneg σ
  have hind_le : ∀ ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) ≤ 2 := ind_le_two σ

  set T : ℕ → ℝ → ℝ := fun f s => ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
    (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) with hT
  set U : ℝ → ℝ := fun s => ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ))) * (ℓ : ℝ) ^ (-s) with hU

  have hweight : ∀ ℓ : ℕ, ℓ ∉ S₀ →
      ((∑ f ∈ (orderOf σ).divisors, (ArithmeticFunction.moebius (orderOf σ / f)) * ((f : ℤ) *
        (degOneCount (E f : IntermediateField ℚ L) ℓ : ℤ)) : ℤ) : ℝ)
        = κ * ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) := by
    intro ℓ hℓS₀
    by_cases hℓ : ℓ.Prime
    · haveI : Fact ℓ.Prime := ⟨hℓ⟩
      obtain ⟨⟨Q₀, hQ₀p, hQ₀l⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) (ratPrimeIdeal ℓ)
      haveI := hQ₀p
      haveI := hQ₀l
      have hQ₀i : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥ := inertia_eq_bot_of_notMem_badPrimes L hℓ hℓS₀ Q₀
      haveI : Finite ((𝓞 L) ⧸ Q₀) :=
        finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
      have hcnt : ∀ f ∈ (orderOf σ).divisors,
          (degOneCount (E f : IntermediateField ℚ L) ℓ : ℤ)
            = ({x : (L ≃ₐ[ℚ] L) ⧸ Subgroup.zpowers (σ ^ (orderOf σ / f)) |
                arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ • x = x}.ncard : ℤ) := by
        intro f _
        rw [degOneCount_of_prime _ hℓ]
        exact_mod_cast
          ncard_degreeOne_primesOver_eq_ncard_frobFixed
            (H := Subgroup.zpowers (σ ^ (orderOf σ / f))) (E := E f) hℓ Q₀ hQ₀i
      rw [Finset.sum_congr rfl fun f hf => by rw [hcnt f hf]]
      rw [weight_eq σ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀),
        ncard_conj_gen_eq_of_orderOf_eq_eight σ _ (by rw [← hn]; exact h8) h3,
        classIndicator_eq_ite σ hℓ hℓS₀ Q₀, classIndicator_eq_ite (σ ^ 5) hℓ hℓS₀ Q₀]
      split_ifs <;> simp [hκ, hcz] <;> ring
    · rw [Finset.sum_congr rfl fun f _ => by rw [degOneCount_of_not_prime _ hℓ],
        classIndicator_of_not_prime σ hℓ, classIndicator_of_not_prime (σ ^ 5) hℓ]
      simp

  have hsummable : ∀ f ∈ (orderOf σ).divisors, ∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ =>
      (if ℓ ∈ S₀ then 0 else (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ))
        * (ℓ : ℝ) ^ (-s)) :=
    fun f _ s hs => (hL (Subgroup.zpowers (σ ^ (orderOf σ / f))) S₀).1 s hs
  have hUsummand : ∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ =>
      (if ℓ ∈ S₀ then 0 else ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ))) * (ℓ : ℝ) ^ (-s)) := by
    intro s hs
    have hsum : Summable (fun ℓ : ℕ => 2 * (ℓ : ℝ) ^ (-s)) :=
      (Real.summable_nat_rpow.mpr (by linarith)).mul_left 2
    refine hsum.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_)
    · split_ifs
      · simp
      · exact mul_nonneg (hind_nonneg ℓ) (Real.rpow_nonneg (Nat.cast_nonneg ℓ) _)
    · have h0 : 0 ≤ (ℓ : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg ℓ) _
      split_ifs
      · simpa using h0
      · exact mul_le_mul_of_nonneg_right (hind_le ℓ) h0
  have hF : ∀ s : ℝ, 1 < s →
      ∑ f ∈ (orderOf σ).divisors,
        ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s = κ * U s := by
    intro s hs
    have hinter : ∑ f ∈ (orderOf σ).divisors,
        ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s
        = ∑' ℓ : ℕ, ∑ f ∈ (orderOf σ).divisors,
            ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
              ((if ℓ ∈ S₀ then 0 else
                (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) := by
      rw [show (∑ f ∈ (orderOf σ).divisors,
          ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s)
          = ∑ f ∈ (orderOf σ).divisors, ∑' ℓ : ℕ,
              ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
                ((if ℓ ∈ S₀ then 0 else
                  (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) from
        Finset.sum_congr rfl fun f _ => tsum_mul_left.symm]
      exact (Summable.tsum_finsetSum
        (fun f hf => ((hsummable f hf s hs).mul_left _))).symm
    rw [hinter, hU, ← tsum_mul_left]
    refine tsum_congr fun ℓ => ?_
    by_cases hℓS₀ : ℓ ∈ S₀
    · simp [hℓS₀]
    · have h := hweight ℓ hℓS₀
      have h2 : ∑ f ∈ (orderOf σ).divisors,
          ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
            ((if ℓ ∈ S₀ then 0 else
              (degOneCount (E f : IntermediateField ℚ L) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
          = (((∑ f ∈ (orderOf σ).divisors,
              (ArithmeticFunction.moebius (orderOf σ / f)) * ((f : ℤ) *
                (degOneCount (E f : IntermediateField ℚ L) ℓ : ℤ)) : ℤ)) : ℝ)
              * (ℓ : ℝ) ^ (-s) := by
        rw [Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [if_neg hℓS₀]
        push_cast
        ring
      rw [h2, h, if_neg hℓS₀]
      ring

  have hO : (fun s : ℝ => (∑ f ∈ (orderOf σ).divisors,
      ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s) + (M : ℝ) *
        Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hsum : ∀ s : ℝ, (∑ f ∈ (orderOf σ).divisors,
        ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) * T f s) + (M : ℝ) *
          Real.log (s - 1)
        = ∑ f ∈ (orderOf σ).divisors,
            ((ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) : ℝ) *
              (T f s + Real.log (s - 1)) := by
      intro s
      rw [hM]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring
    refine (Asymptotics.IsBigO.fun_sum fun f _ => ?_).congr'
      (Eventually.of_forall fun s => (hsum s).symm) EventuallyEq.rfl
    exact ((hL (Subgroup.zpowers (σ ^ (orderOf σ / f))) S₀).2).const_mul_left _
  have hO2 : (fun s : ℝ => κ * U s + (M : ℝ) * Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine hO.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    rw [hF s hs]

  have hcoef : (M : ℝ) / κ
      = 2 * (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) / (Nat.card (L ≃ₐ[ℚ] L) : ℝ) := by
    have hos := card_setOf_isConj_mul_card_centralizer σ
    have hG0 : (0 : ℝ) < Nat.card (L ≃ₐ[ℚ] L) := by exact_mod_cast Nat.card_pos
    have hos' : ((Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℕ) : ℝ) * (cz : ℝ)
        = (Nat.card (L ≃ₐ[ℚ] L) : ℝ) := by rw [hcz]; exact_mod_cast hos
    rw [div_eq_div_iff hκ0.ne' hG0.ne', hM4, hκ, ← hos']
    push_cast
    ring
  have hO3 : (fun s : ℝ => U s + ((M : ℝ) / κ) * Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine (hO2.const_mul_left κ⁻¹).congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    show κ⁻¹ * (κ * U s + (M : ℝ) * Real.log (s - 1)) = U s + (M : ℝ) / κ * Real.log (s - 1)
    field_simp

  have hsplit : ∀ s : ℝ, 1 < s →
      (∑' ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
        = U s + ∑ ℓ ∈ S₀, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
    intro s hs
    have hfin : ∀ ℓ ∉ S₀, (if ℓ ∈ S₀ then ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) else 0) = 0 :=
      fun ℓ hℓ => if_neg hℓ
    have hdecomp : ∀ ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)
        = (if ℓ ∈ S₀ then 0 else ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ))) * (ℓ : ℝ) ^ (-s)
          + (if ℓ ∈ S₀ then ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) else 0) := by
      intro ℓ; split_ifs <;> simp
    rw [tsum_congr hdecomp, (hUsummand s hs).tsum_add (summable_of_ne_finset_zero hfin),
      tsum_eq_sum hfin]
    refine congrArg _ (Finset.sum_congr rfl fun ℓ hℓ => ?_)
    rw [if_pos hℓ]
  have hbad : (fun s : ℝ => ∑ ℓ ∈ S₀, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (2 * S₀.card : ℝ) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    rw [Real.norm_eq_abs, norm_one, mul_one,
      abs_of_nonneg (Finset.sum_nonneg fun ℓ _ => mul_nonneg (hind_nonneg ℓ) (Real.rpow_nonneg (Nat.cast_nonneg ℓ) _))]
    have : ∀ ℓ ∈ S₀, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) ≤ 2 := by
      intro ℓ _
      have h0 : 0 ≤ (ℓ : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg ℓ) _
      have h1 : (ℓ : ℝ) ^ (-s) ≤ 1 := by
        rcases Nat.eq_zero_or_pos ℓ with h0' | hpos
        · subst h0'; rw [Nat.cast_zero, Real.zero_rpow (by linarith : -s ≠ 0)]; exact zero_le_one
        · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpos) (by linarith)
      nlinarith [hind_le ℓ, hind_nonneg ℓ]
    calc ∑ ℓ ∈ S₀, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) ≤ ∑ _ℓ ∈ S₀, (2 : ℝ) := Finset.sum_le_sum this
      _ = 2 * S₀.card := by simp [mul_comm]
  refine ((hO3.add hbad).congr' ?_ EventuallyEq.rfl)
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  show U s + (M : ℝ) / κ * Real.log (s - 1) + ∑ ℓ ∈ S₀, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)
    = (∑' ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) + _ * Real.log (s - 1)
  rw [hsplit s hs, hcoef]
  ring

end FltWs24.DivisionDensity

open LanglandsTunnell in
theorem solution
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ =>
        (∑' ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + (2 * (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) / (Nat.card (L ≃ₐ[ℚ] L) : ℝ))
        * Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) :=
  FltWs24.DivisionDensity.towerDirichletDensity_add_of_orderOf_eq_eight σ h8 h3

end S_LanglandsTunnell_towerDirichletDensity_add_of_orderOf_eq_eight
end P2MW
export P2MW.S_LanglandsTunnell_towerDirichletDensity_add_of_orderOf_eq_eight (solution)
