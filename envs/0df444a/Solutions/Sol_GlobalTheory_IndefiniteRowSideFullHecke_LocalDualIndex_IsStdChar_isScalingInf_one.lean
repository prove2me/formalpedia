-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar.isScalingInf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:53.599375+00:00
-- url     : https://prove2.me/submissions/6c843918-0898-4188-81a6-f32cd9d48ce3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LocalDualIndex_isScalingInf_of_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
namespace IsStdChar
theorem _root_.solution {ψ₀ : AddChar (AF F) ℂ} (h₀ : IsStdChar F ψ₀) :
    IsScalingInf F ψ₀ 1 :=
  isScalingInf_of_eq F h₀ fun x => by rw [map_one, one_mul]
end IsStdChar
end GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
