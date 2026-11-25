-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.stabVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:09:17.967701+00:00
-- url     : https://prove2.me/submissions/08e2f43d-9587-4d1a-a70a-0d32106946d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.SelfDualLatticeCompare
theorem _root_.solution (x : SelfDualLatticeActions.Wv E v M) :
    UnitaryLatticeOrthogonal.stabVec σ J v x = SelfDualLatticeActions.vecStab v σ J x := rfl
end GlobalTheory.SelfDualLatticeCompare
