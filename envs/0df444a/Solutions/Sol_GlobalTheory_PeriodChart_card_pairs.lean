-- Prove2me | solution 1 for GlobalTheory.PeriodChart.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:28.197606+00:00
-- url     : https://prove2.me/submissions/16ce493a-094e-4711-b20d-b229b300bac0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_conj_rt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodChart
theorem _root_.solution {p q : ℕ} (hty : IsTypeFn H p q ty) :
    Nat.card {x : Fin g × Fin g // ty x.1 = ComplexEmbedding.conjugate (ty x.2)} = finrank ℚ E * p * q := by
  classical
  have hN : ∀ τ : E →+* ℂ, (Finset.univ.filter (fun i : Fin g => ty i = τ)).card *
      (Finset.univ.filter (fun i : Fin g => ty i = ComplexEmbedding.conjugate τ)).card = p * q := by
    intro τ
    have h1 := hty τ
    have h2 := hty (ComplexEmbedding.conjugate τ)
    have hc := conj_rt H τ
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1 h2
    by_cases hτ : τ (H.rt : E) = H.rt0
    · rw [h1.1 hτ, h2.2 (hc.1 hτ)]
    · rw [h1.2 hτ, h2.1 (not_not.1 (mt hc.2 hτ)), mul_comm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := fun x : Fin g × Fin g => ty x.2) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  have hfib : ∀ τ : E →+* ℂ, ((Finset.univ.filter fun x : Fin g × Fin g =>
      ty x.1 = ComplexEmbedding.conjugate (ty x.2)).filter (fun x => ty x.2 = τ)).card = p * q := by
    intro τ
    rw [← hN τ, mul_comm, ← Finset.card_product]
    congr 1
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, h2], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, h2], h2⟩
  rw [Finset.sum_congr rfl (fun τ _ => hfib τ), Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, smul_eq_mul]
  ring
end GlobalTheory.PeriodChart
