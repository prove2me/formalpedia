-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabEq.act_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:51.526999+00:00
-- url     : https://prove2.me/submissions/977945ee-6cd8-4302-96ea-a9f3733bc6ec

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
theorem _root_.solution (g : HA (Fv F v) σ J) (x y : Fin M → Ev F E v) (a : Ev F E v) :
    act σ J v g (y - a • x) = act σ J v g y - a • act σ J v g x := by
  unfold act
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
end GlobalTheory.UnitVectorStabEq
