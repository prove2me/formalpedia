-- Prove2me | solution 1 for GlobalTheory.QNorm.mem_sUnits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:51.785715+00:00
-- url     : https://prove2.me/submissions/0f0af28a-a2a2-4378-827a-9c0c6b7ebc96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.QNorm
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) :
    x ∈ sUnits F S ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F (x : F) = 1 :=
  Iff.rfl
end GlobalTheory.QNorm
