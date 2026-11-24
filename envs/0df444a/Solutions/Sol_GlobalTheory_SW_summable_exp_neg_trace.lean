-- Prove2me | solution 1 for GlobalTheory.SW.summable_exp_neg_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:38:59.961109+00:00
-- url     : https://prove2.me/submissions/11945e28-a885-4167-a032-b2e49cf2825e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitian
import Theorems.Thm_GlobalTheory_SW_PosSum_norm_entry_le_trace
import Theorems.Thm_GlobalTheory_SW_PosSum_exists_repr_le
import Theorems.Thm_GlobalTheory_SW_PosSum_house_le_of_isType
import Theorems.Thm_GlobalTheory_Koecher_summable_exp_neg_mul_sum_abs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory.SW.PosSum
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N c : ℕ) (δ : ℝ), 0 < c → 0 < δ → Summable fun T : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef} => Real.exp (-(δ * ∑ τ : Ψ, (T.1.map τ.1).trace.re)) := by
  intro E _ _ _ Ψ hΨ N c δ hc hδ
  obtain ⟨C, hC, hb⟩ := exists_repr_le E
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let K : ℝ := Fintype.card ι * (C * c) + 1
  have hK : 0 < K := by positivity
  let m : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧
      ∀ τ : Ψ, (T.map τ.1).PosSemidef} → ι → ℤ := fun T q =>
    (RingOfIntegers.basis E).repr ⟨_, T.2.2.1 q.1 q.2.1⟩ q.2.2
  have hm : Function.Injective m := by
    intro T T' h
    ext a b
    have : (⟨_, T.2.2.1 a b⟩ : 𝓞 E) = ⟨_, T'.2.2.1 a b⟩ :=
      (RingOfIntegers.basis E).ext_elem fun j => congrFun h (a, b, j)
    have h2 : (c : E) * T.1 a b = c * T'.1 a b := congrArg Subtype.val this
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hc.ne') h2
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun T => ?_)
    ((GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := ι) (div_pos hδ hK)).comp_injective hm)
  set S := ∑ τ : Ψ, (T.1.map τ.1).trace.re with hS
  have h0 : ∀ τ : Ψ, 0 ≤ (T.1.map τ.1).trace.re := fun τ =>
    (Complex.nonneg_iff.1 (T.2.2.2 τ).trace_nonneg).1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => h0 τ
  have hq : ∀ q, |(m T q : ℝ)| ≤ C * c * S := fun q => by
    refine (hb _ _).trans ?_
    change C * house ((c : E) * T.1 q.1 q.2.1) ≤ _
    rw [house_nat_mul, mul_assoc]
    gcongr
    refine house_le_of_isType hΨ hS0 fun τ hτ => ?_
    exact (norm_entry_le_trace (T.2.2.2 ⟨τ, hτ⟩) q.1 q.2.1).trans
      (Finset.single_le_sum (fun τ _ => h0 τ) (Finset.mem_univ (⟨τ, hτ⟩ : Ψ)))
  have hs : ∑ q, |(m T q : ℝ)| ≤ K * S := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun q _ => hq q).trans ?_
    simp only [Finset.card_univ, nsmul_eq_mul, K]
    nlinarith
  simp only [Function.comp_apply]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  calc δ / K * ∑ q, |(m T q : ℝ)| ≤ δ / K * (K * S) := by gcongr
    _ = δ * S := by field_simp
end GlobalTheory.SW
