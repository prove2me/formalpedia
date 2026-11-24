-- Prove2me | solution 1 for GlobalTheory.KSp.exists_integral_cball_char_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:58.637997+00:00
-- url     : https://prove2.me/submissions/73a1c614-15f2-4f64-9655-d293c481a74e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralClosedBallAddCharEqZero
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution :
    ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  intro F _ _ _ _ _ _ _ lam _ ψ _ _ hne
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext x; simpa using h x)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by simp)
  refine ⟨Units.mk0 t ht0, fun s hs => ?_⟩
  have hs' : t ∈ GlobalTheory.SplitWeil.cball s := hs
  have hm : MeasurableSet (GlobalTheory.SplitWeil.cball s) := (GlobalTheory.SplitWeil.isOpen_cball s).measurableSet
  have hadd : ∀ x y : F, x ∈ GlobalTheory.SplitWeil.cball s → y ∈ GlobalTheory.SplitWeil.cball s →
      x + y ∈ GlobalTheory.SplitWeil.cball s := fun x y hx hy => by
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  have hneg : -t ∈ GlobalTheory.SplitWeil.cball s := by
    simpa [GlobalTheory.SplitWeil.cball] using hs'
  have hiff : ∀ x : F, t + x ∈ GlobalTheory.SplitWeil.cball s ↔ x ∈ GlobalTheory.SplitWeil.cball s := fun x =>
    ⟨fun h => by simpa using hadd _ _ hneg h, fun h => hadd _ _ hs' h⟩
  rw [← integral_indicator hm]
  have h1 := integral_add_left_eq_self (μ := lam)
    ((GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x)) t
  have h2 : (fun x => (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) (t + x))
      = fun x => ψ t * (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x := by
    funext x
    by_cases hx : x ∈ GlobalTheory.SplitWeil.cball s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), AddChar.map_add_eq_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h)), mul_zero]
  rw [h2, integral_const_mul] at h1
  have h3 : (ψ t - 1) * ∫ x, (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x ∂lam = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ht)
end GlobalTheory.KSp
