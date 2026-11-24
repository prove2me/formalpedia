-- Prove2me | solution 1 for GlobalTheory.SW.Vac.ip_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:23.162236+00:00
-- url     : https://prove2.me/submissions/2bd6ebda-f254-401e-b24a-d9002eab71a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (c : ℂ) (hc : c ≠ 0) (φ : Matrix κ ι ℚ → ℂ) :
    ip (c • φ) (c • φ) = c * conj c * ip φ φ := by
  have hcc : c * conj c ≠ 0 := mul_ne_zero hc (by simpa using hc)
  have key : ∀ (d : ℂ), d ≠ 0 → ∀ ψ : Matrix κ ι ℚ → ℂ, haar (fun x => d * ψ x) = d * haar ψ := by
    intro d hd ψ
    have hp : (fun R : ℕ => 0 < R ∧ HasLevel R (fun x => d * ψ x)) =
        fun R : ℕ => 0 < R ∧ HasLevel R ψ := by
      funext R; simp [HasLevel, hd]
    have hch : ∀ (p q : ℕ → Prop) (h : ∃ R, p R) (h' : ∃ R, q R), p = q → h.choose = h'.choose := by
      intro p q h h' e; subst e; rfl
    have hiff : IsSB (fun x => d * ψ x) ↔ IsSB ψ := by
      unfold IsSB; rw [hp]
    unfold haar
    by_cases h : IsSB ψ
    · rw [dif_pos h, dif_pos (hiff.2 h), hch _ _ (hiff.2 h) h hp]
      unfold haarAt
      rw [← mul_finsum]; ring
    · rw [dif_neg h, dif_neg (mt hiff.1 h), mul_zero]
  unfold ip
  rw [← key _ hcc]
  congr 1; funext x; simp; ring
end GlobalTheory.SW.Vac
