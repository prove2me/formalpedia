-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeSplit.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:24.406707+00:00
-- url     : https://prove2.me/submissions/3346f1fb-3e4a-49fa-8644-4a7f4901acd3

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
theorem _root_.solution (x y : Fin M → Ev F E v) : y ∈ perp σ J v x ↔ hR (Fv F v) σ J x y = 0 :=
  Iff.rfl
end GlobalTheory.SelfDualLatticeSplit
