-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.sL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:38.162137+00:00
-- url     : https://prove2.me/submissions/da204e06-7e8b-4580-bce7-fd033f477d44

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
theorem _root_.solution (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (β : Fv F v) :
    UnitaryLatticeOrthogonal.SL σ J v L β = SelfDualLatticeActions.sphere v σ J L β := rfl
end GlobalTheory.SelfDualLatticeCompare
