-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.end_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:56.931982+00:00
-- url     : https://prove2.me/submissions/56a1ce21-10cd-4a8a-9eaa-60205ee544af

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
theorem _root_.solution (hF : IsFrame h δ e f W) {A B : Module.End L V} (he : ∀ i, A (e i) = B (e i))
    (hf : ∀ i, A (f i) = B (f i)) (hw : ∀ w ∈ W, A w = B w) : A = B := by
  ext x
  obtain ⟨a, b, w, hwW, rfl⟩ := hF.2.2.2.2.2 x
  simp [map_add, map_sum, he, hf, hw w hwW]
end GlobalTheory.CompanionTheory.Iwahori
