-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.isScalingInf_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:39:40.741135+00:00
-- url     : https://prove2.me/submissions/a943ce80-39dc-4475-b017-d92aee9e8557

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex

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
theorem _root_.solution {ψ₀ ψ : AddChar (AF F) ℂ} (h₀ : IsStdChar F ψ₀) {a : F}
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) : IsScalingInf F ψ a := by
  intro x
  rw [← h₀.2, psiInf, psiInf, h]
  congr 1
  exact Prod.ext rfl (mul_zero _)
end GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
