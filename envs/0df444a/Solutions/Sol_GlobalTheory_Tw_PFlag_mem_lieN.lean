-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_lieN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:45.834815+00:00
-- url     : https://prove2.me/submissions/3e385a16-bb62-48ea-a63d-7583358c6410

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
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)
variable {F}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieN ↔ ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V := Iff.rfl
end GlobalTheory.Tw.PFlag
