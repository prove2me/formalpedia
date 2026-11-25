-- Prove2me | solution 1 for GlobalTheory.PeriodExists.exists_typeFn_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:23.744942+00:00
-- url     : https://prove2.me/submissions/ba734d44-a67f-49de-adb1-cab2719340a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty
import Theorems.Thm_GlobalTheory_PeriodExists_card_cmType
import Theorems.Thm_GlobalTheory_PeriodExists_exists_imaginary
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_FramePeriod_cmType
import Theorems.Thm_GlobalTheory_FramePeriod_isPeriod_frame
import Theorems.Thm_GlobalTheory_T_signature_hermitian_model_of_datum
import Theorems.Thm_GlobalTheory_exists_herm_coord_of_datum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_lminor_diagonal
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
open GlobalTheory GlobalTheory.PeriodExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodExists
theorem _root_.solution (H : Host E) (D : Datum H) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty ∧
      g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  classical
  obtain ⟨ξ, hξ, hξ0, hpos⟩ := exists_imaginary H
  obtain ⟨Gm, φ, hm⟩ := exists_herm_coord_of_datum E H D ξ hξ hξ0 _ rfl
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0
  have hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => by simp [Ψ]
  let idx := (Fintype.equivFin (Ψ × Fin (D.p + D.q))).symm
  obtain ⟨h1, h2⟩ := FramePeriod.isPeriod_frame E H D _ ξ Gm φ Ψ hΨ _ idx _ (fun _ => rfl) hξ
    (fun τ hτ => hpos τ ((hΨ τ).1 hτ)) hm rfl
  choose Q hQ hG using fun τ : Ψ =>
    (GlobalTheory.T.signature_hermitian_model_of_datum E H D _ ξ Gm φ hξ hm τ.1 ((hΨ _).1 τ.2)).1 (hpos _ ((hΨ _).1 τ.2))
  have hx : (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) ∈ FD.GG Ψ Gm D.q := by
    intro τ
    refine ⟨hQ τ, fun i => ?_⟩
    have h3 : FD.dmin Gm (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) τ i = ((FD.psgn D.q i : ℝ) : ℂ) := by
      change FD.lminor (FD.gram τ.1 Gm (Q τ)) i = _
      rw [hG, FD.FrameDegreeData.lminor_diagonal, FD.psgn, ← Fin.prod_univ_eq_prod_range]
      push_cast
      rfl
    rw [h3, Complex.ofReal_re]
    refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    unfold FD.sgn
    split_ifs <;> norm_num
  obtain ⟨⟨P, hP⟩, h4⟩ := h2 _ hx
  refine ⟨_, _, h1, ?_, P, h4 P hP⟩
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
    card_cmType Ψ (FramePeriod.cmType H Ψ hΨ)]
end GlobalTheory.PeriodExists
