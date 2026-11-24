-- Prove2me | solution 1 for GlobalTheory.FramePeriod.isTypeFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:08.447955+00:00
-- url     : https://prove2.me/submissions/220410bd-ec0b-4f77-a7f1-eb710758c1c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_FramePeriod_cmType
import Theorems.Thm_GlobalTheory_FramePeriod_card_fibre
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution (H : Host E) (p q : ℕ) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ))
    (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < q then ComplexEmbedding.conjugate (idx k).1.1
      else (idx k).1.1) (hr : r = p + q) : IsTypeFn H p q ty := by
  have hcm := cmType H Ψ hΨ
  have hq : Fintype.card {a : Fin r // (a : ℕ) < q} = q := by
    rw [Fintype.card_subtype, Fin.card_filter_val_lt]; omega
  intro τ
  rw [ne_eq, ← hΨ]
  constructor
  · intro hτ
    rw [card_fibre idx ⟨τ, hτ⟩ _ (fun a => ¬ (a : ℕ) < q), Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, hq, Fintype.card_fin]
    · omega
    · intro k
      rw [hty]
      split_ifs with hk
      · simp only [hk, not_true, and_false, iff_false]
        intro h
        exact (hcm _).1 (idx k).1.2 (h ▸ hτ)
      · simp [hk, Subtype.ext_iff]
  · intro hτ
    have hτ' : ComplexEmbedding.conjugate τ ∈ Ψ := by
      by_contra h; exact hτ ((hcm τ).2 h)
    rw [card_fibre idx ⟨_, hτ'⟩ _ (fun a => (a : ℕ) < q), Nat.card_eq_fintype_card, hq]
    intro k
    rw [hty]
    split_ifs with hk
    · simp only [hk, and_true, Subtype.ext_iff]
      constructor
      · rintro rfl; exact (ComplexEmbedding.involutive_conjugate E _).symm
      · intro h; rw [h]; exact ComplexEmbedding.involutive_conjugate E _
    · simp only [hk, and_false, iff_false]
      intro h
      exact hτ (h ▸ (idx k).1.2)
end GlobalTheory.FramePeriod
