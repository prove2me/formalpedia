-- Prove2me | solution 1 for GroundTheory.Global.under_eq_of_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:50:17.086386+00:00
-- url     : https://prove2.me/submissions/524106c2-fc44-4721-8f5b-173afc0f936c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_FunctionFieldIntegral
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_BadPrimesFinite

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
open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve.Affine
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 K) = v :=
  HeightOneSpectrum.ext h.over.symm
end GroundTheory.Global
