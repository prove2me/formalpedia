-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.isNilpotent_of_mem_lieN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:24.786221+00:00
-- url     : https://prove2.me/submissions/1dcb493f-f754-4b34-9b2f-478df54bdb23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) : IsNilpotent X := by
  have key : ∀ V : Submodule k (Fin n → k), V ∈ F.carrier → V ≤ Module.End.maxGenEigenspace (Matrix.toLin' X) 0 := by
    intro V
    induction V using WellFoundedLT.induction with
    | ind V ih =>
      intro hV v hv
      have h1 : F.pred V ≤ Module.End.maxGenEigenspace (Matrix.toLin' X) 0 := sSup_le fun V' h => ih V' h.2 h.1
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (h1 (hX V hV v hv))
      refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m + 1, ?_⟩
      simpa [pow_succ] using hm
  have h2 : IsNilpotent (Matrix.toLin' X) := Module.End.isNilpotent_iff_of_finite.2 fun v => by
    simpa using (Module.End.mem_maxGenEigenspace _ _ _).1 (key ⊤ F.top_mem (Submodule.mem_top (x := v)))
  exact (IsNilpotent.map_iff (f := Matrix.toLinAlgEquiv') Matrix.toLinAlgEquiv'.injective).1 h2
end GlobalTheory.Tw.PFlag
