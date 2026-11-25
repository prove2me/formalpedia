-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.placesOver_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:20.869862+00:00
-- url     : https://prove2.me/submissions/c3c6c83a-bba4-456e-8443-8577718f6aed

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}
omit [NumberField K]
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    {v v' : HeightOneSpectrum (𝓞 K)} (h : v' = v) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) (hw' : w.asIdeal.LiesOver v'.asIdeal) :
    yf v' ⟨w, hw'⟩ = yf v ⟨w, hw⟩ := by
  subst h
  rfl
end GroundTheory.Global.IdeleNorm
