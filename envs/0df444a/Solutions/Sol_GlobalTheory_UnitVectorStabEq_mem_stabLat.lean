-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabEq.mem_stabLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:12.721376+00:00
-- url     : https://prove2.me/submissions/9aa9100c-2fb6-41ac-bbcb-8b69326d0e70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabEq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.UnitVectorStabEq
theorem _root_.solution (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (g : HA (Fv F v) σ J) :
    g ∈ stabLat σ J v L ↔ ∀ y, y ∈ L ↔ act σ J v g y ∈ L := Iff.rfl
end GlobalTheory.UnitVectorStabEq
