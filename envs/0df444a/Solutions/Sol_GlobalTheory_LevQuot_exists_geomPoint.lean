-- Prove2me | solution 1 for GlobalTheory.LevQuot.exists_geomPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:41:27.866338+00:00
-- url     : https://prove2.me/submissions/3951f36b-cb65-4b2a-b1d5-5d452aac379e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}
namespace GlobalTheory.LevQuot
theorem _root_.solution (Z : Scheme.{0}) (z : Z) : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k)
    (w : Spec (CommRingCat.of k) ⟶ Z) (p : Spec (CommRingCat.of k)), w p = z := by
  let K := AlgebraicClosure (Z.residueField z)
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z, p, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
end GlobalTheory.LevQuot
