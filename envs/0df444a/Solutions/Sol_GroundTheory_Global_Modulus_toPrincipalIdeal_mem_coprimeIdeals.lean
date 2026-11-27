-- Prove2me | solution 1 for GroundTheory.Global.Modulus.toPrincipalIdeal_mem_coprimeIdeals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:46:32.134954+00:00
-- url     : https://prove2.me/submissions/f7ffe919-3d8b-402e-bd37-dd1e3bc1a8e6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_RayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_IdealRayClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
namespace GroundTheory.Global.Modulus
theorem _root_.solution {a : Kˣ} (ha : a ∈ 𝔪.rayUnits) :
    toPrincipalIdeal (𝓞 K) K a ∈ 𝔪.coprimeIdeals := by
  rw [← toFractionalIdeal_diagonal]
  exact 𝔪.toFractionalIdeal_mem_coprimeIdeals ha
end GroundTheory.Global.Modulus
