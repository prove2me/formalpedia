-- Prove2me | solution 1 for GlobalTheory.AnArc.period_clauses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:34:21.884249+00:00
-- url     : https://prove2.me/submissions/b5c4c914-3ea8-449c-991f-ca9c7c32888a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_PolarisedLattice_lattice_of_im
import Theorems.Thm_GlobalTheory_AnArc_EF_bijective
import Theorems.Thm_GlobalTheory_AnArc_finrank_La
import Theorems.Thm_GlobalTheory_AnArc_Hw_pos
import Theorems.Thm_GlobalTheory_AnArc_im_Hw_Pw
import Theorems.Thm_GlobalTheory_AnArc_HwMat_isHermitian
import Theorems.Thm_GlobalTheory_AnArc_hermForm_HwMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) {L : Type}
    [AddCommGroup L] (e : L ≃+ A.La) (P : L →+ (Fin g → ℂ)) (hP : ∀ x, P x = h (A.Pw w (e x))) :
    Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        ∀ x y, (hermForm Hm (P x) (P y)).im = A.EF (e x) (e y) := by
  let P' : A.La →+ (Fin g → ℂ) := h.toLinearMap.toAddMonoidHom.comp (A.Pw w)
  have hr : Module.finrank ℤ A.La = Module.finrank ℝ (Fin g → ℂ) :=
    A.finrank_La.trans (h.restrictScalars ℝ).finrank_eq
  obtain ⟨h1, h2, h3⟩ := PolarisedLattice.lattice_of_im A.EF A.EF_bijective.1 P'
    (fun z => (A.Hw w).flip (h.symm z) ∘ₗ h.symm.toLinearMap)
    (fun a b => by simpa [P'] using A.im_Hw_Pw hw a b) hr
  have hPP : (P : L → _) = P' ∘ e := funext hP
  have hrange : Set.range P = Set.range P' := by rw [hPP, e.surjective.range_comp]
  have hrange' : P.range = P'.range := SetLike.coe_injective hrange
  refine ⟨hPP ▸ h1.comp e.injective, hrange' ▸ h2, hrange ▸ h3, A.HwMat w h, A.HwMat_isHermitian w h,
    fun z hz => ?_, fun x y => ?_⟩
  · obtain ⟨v, rfl⟩ := h.surjective z
    rw [hermForm_HwMat]
    exact A.Hw_pos hw fun hv => hz (by simp [hv])
  · rw [hP, hP, hermForm_HwMat, A.im_Hw_Pw hw]
end GlobalTheory.AnArc
