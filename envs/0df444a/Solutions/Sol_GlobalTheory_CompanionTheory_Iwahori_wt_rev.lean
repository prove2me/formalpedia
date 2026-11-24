-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.wt_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:55.120985+00:00
-- url     : https://prove2.me/submissions/20cd241a-25a4-4cd3-8937-c52a6462ffce

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori
variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.Iwahori
theorem _root_.solution {l : ℕ} (i : Idx l) : wt (rev i) + wt i = 2 * l := by
  rcases i with _ | i | i
  · simp only [wt, rev]; omega
  · simp only [wt, rev]; have := i.2; omega
  · simp only [wt, rev]; have := i.2; omega
end GlobalTheory.CompanionTheory.Iwahori
