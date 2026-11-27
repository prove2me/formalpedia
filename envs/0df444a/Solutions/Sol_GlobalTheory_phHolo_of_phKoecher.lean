-- Prove2me | solution 1 for GlobalTheory.phHolo_of_phKoecher
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:19.188824+00:00
-- url     : https://prove2.me/submissions/58b7eb09-3379-43ff-9675-9540e0974411

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_spInvariant_transl
import Theorems.Thm_GlobalTheory_spInvariant_conj
import Theorems.Thm_GlobalTheory_siegel_eq_of_bounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
namespace GlobalTheory
theorem _root_.solution : PhKoecherStatement → PhHoloStatement := by
  intro hK g hg H hol hH
  have hb := hK g hg 1 le_rfl H hol
    (fun B hB τ hτ => by simpa using spInvariant_transl hH hB hτ)
    (fun U hU _ τ hτ => by
      obtain ⟨U, rfl⟩ := (isUnit_iff_isUnit_det U).2 (hU ▸ isUnit_one)
      exact spInvariant_conj hH U hτ)
  by_cases h : (SiegelH (Fin g)).Nonempty
  · obtain ⟨σ, hσ⟩ := h
    exact ⟨H σ, fun τ hτ => siegel_eq_of_bounded hol hH hb hτ hσ⟩
  · exact ⟨0, fun τ hτ => absurd ⟨τ, hτ⟩ h⟩
end GlobalTheory
