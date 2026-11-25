-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.galEquiv_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:50.002833+00:00
-- url     : https://prove2.me/submissions/817038ee-c5ba-4571-a542-be50d6333fec

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois

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
open IsDedekindDomain NumberField WithZero Topology Filter TensorProduct
open scoped Pointwise
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) (x : L) :
    galEquiv v σ w w' h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) (σ x) :=
  galHom_algebraMap σ w w' h x
end GroundTheory.Global.SemiLocal
