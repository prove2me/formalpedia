-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.map_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:59.898794+00:00
-- url     : https://prove2.me/submissions/ea848bf5-91e0-4335-85af-e98cff65a175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
omit [NumberField F] [NumberField E]
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (c : E ≃ₐ[F] E)
    (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.TensorProduct.map p (AlgHom.id F E) (sg A c z) =
      sg B c (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sg]
  | add x y h1 h2 => simp only [map_add, h1, h2]
end GlobalTheory.AdLat.RootNear
