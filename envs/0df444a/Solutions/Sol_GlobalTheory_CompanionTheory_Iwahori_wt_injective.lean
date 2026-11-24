-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.wt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:53.050866+00:00
-- url     : https://prove2.me/submissions/c70efa20-7917-482d-9fd7-f833d0b422bf

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
theorem _root_.solution {l : ℕ} : Function.Injective (wt : Idx l → ℕ) := by
  rintro (_ | i | i) (_ | j | j) hij <;> simp only [wt] at hij <;>
    first
    | rfl
    | (exfalso; have := i.2; omega)
    | (exfalso; have := j.2; omega)
    | (exfalso; have := i.2; have := j.2; omega)
    | (congr 2; apply Fin.ext; have := i.2; have := j.2; omega)
end GlobalTheory.CompanionTheory.Iwahori
