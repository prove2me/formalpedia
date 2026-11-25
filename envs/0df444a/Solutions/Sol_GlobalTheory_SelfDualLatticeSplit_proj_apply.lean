-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeSplit.proj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:30.375655+00:00
-- url     : https://prove2.me/submissions/67cca191-0d70-4822-94fd-46183613c014

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength

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
open GlobalTheory GlobalTheory.SelfDualLatticeSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.SelfDualLatticeSplit
theorem _root_.solution (x : Fin M → Ev F E v) (b : Ev F E v) (y : Fin M → Ev F E v) :
    proj σ J v x b y = y - (b * hR (Fv F v) σ J x y) • x := rfl
end GlobalTheory.SelfDualLatticeSplit
