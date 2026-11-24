-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabEq.mem_stabVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:13.441077+00:00
-- url     : https://prove2.me/submissions/66995078-a96f-4ff8-986f-4da65d4363ff

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
theorem _root_.solution (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) :
    g ∈ stabVec σ J v x ↔ act σ J v g x = x := by
  unfold stabVec
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩
end GlobalTheory.UnitVectorStabEq
