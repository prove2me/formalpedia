-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.isSDLatIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:22.821748+00:00
-- url     : https://prove2.me/submissions/68b28526-5698-4635-b710-0bd7fcfd208d

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
theorem _root_.solution (P : Submodule (SelfDualLatticeActions.Ev E v) (SelfDualLatticeActions.Wv E v M))
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.IsSDLatIn σ J v P L ↔ SelfDualLatticeActions.IsSelfDualIn v σ J P L := Iff.rfl
end GlobalTheory.SelfDualLatticeCompare
