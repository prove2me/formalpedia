-- Prove2me | solution 1 for GlobalTheory.ChF.formalDisc_points_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:18.925451+00:00
-- url     : https://prove2.me/submissions/d4fafdfc-89a7-4270-a2b0-f03b32ab7f64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalDiscPointsValuationIntegers
import Theorems.Thm_GlobalTheory_NilpotentEval_exists_pow_sup_span_le
import Theorems.Thm_GlobalTheory_NilpotentEval_pow_mul_le
import Theorems.Thm_GlobalTheory_mvPowerSeries_eval_of_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.ChF
private theorem exists_pow_mem_span_of_not_isUnit {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
    [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {x : O} (hx : ¬ IsUnit x) :
    ∃ M : ℕ, x ^ M ∈ Ideal.span {(p : O)} := by
  have h1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have hp : (0 : NNReal) < v (algebraMap O C (p : O)) := by
    rw [map_natCast, pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨M, hM⟩ := NNReal.exists_pow_lt_of_lt_one hp h1
  refine ⟨M, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
  rw [map_pow, map_pow]
  exact hM.le
private theorem not_isUnit_algHom_of_constantCoeff_eq_zero {O : Type} [CommRing O] [Nontrivial O]
    {κ : Type} (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O)
    (hf : MvPowerSeries.constantCoeff f = 0) : ¬ IsUnit (Φ f) := by
  rintro ⟨u, hu⟩
  have h1 : IsUnit (1 - ((u⁻¹ : Oˣ) : O) • f) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_sub, map_one, Algebra.smul_def, map_mul, hf,
      mul_zero, sub_zero]
    exact isUnit_one
  have h2 := h1.map Φ
  rw [map_sub, map_one, map_smul, ← hu, smul_eq_mul, Units.inv_mul, sub_self] at h2
  exact not_isUnit_zero h2
end GlobalTheory.ChF
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (κ : Type) [Finite κ], (∀ c : κ → O, (∀ q, ¬ IsUnit (c q)) → ∃! Φ : MvPowerSeries κ O →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q) ∧ (∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f)) ∧ ∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (n : ℕ), ∃ N : ℕ, ∀ f ∈ ((Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* MvPowerSeries κ O) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ O))) ^ N, Φ f ∈ Ideal.span {(p : O) ^ n} := by
  intro p _ C _ _ _ v O _ _ hv hp hc κ _
  haveI : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hp.out (isUnit_of_subsingleton _)
  refine ⟨fun c hcu => ?_, not_isUnit_algHom_of_constantCoeff_eq_zero, fun Φ n => ?_⟩
  · obtain ⟨hex, huniq⟩ := GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) κ c
      fun j => exists_pow_mem_span_of_not_isUnit hv (hcu j)
    obtain ⟨Φ, hΦ⟩ := hex hc O
    refine ⟨Φ, hΦ, fun Ψ hΨ => ?_⟩
    have := huniq inferInstance O Ψ.toRingHom Φ.toRingHom
      (fun t => (Ψ.commutes t).trans (Φ.commutes t).symm) hΨ hΦ
    exact AlgHom.ext fun g => DFunLike.congr_fun this g
  · obtain ⟨N, hN⟩ := GlobalTheory.NilpotentEval.exists_pow_sup_span_le (Ideal.span {(p : O)})
      (fun q => Φ (MvPowerSeries.X q)) fun q => exists_pow_mem_span_of_not_isUnit hv
        (not_isUnit_algHom_of_constantCoeff_eq_zero Φ _ (MvPowerSeries.constantCoeff_X q))
    refine ⟨N * n, fun f hf => ?_⟩
    rw [← Ideal.span_singleton_pow]
    refine GlobalTheory.NilpotentEval.pow_mul_le hN n ?_
    have hf' := Ideal.mem_map_of_mem Φ.toRingHom hf
    rw [Ideal.map_pow] at hf'
    refine Ideal.pow_right_mono ?_ _ hf'
    rw [Ideal.map_sup]
    refine sup_le_sup ?_ ?_
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have : (Φ.toRingHom.comp MvPowerSeries.C) x = x := Φ.commutes x
      rwa [this]
    · rw [Ideal.map_span]
      refine Ideal.span_mono ?_
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, rfl⟩
end GlobalTheory.ChF
