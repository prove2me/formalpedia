-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.piGal_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:47.588174+00:00
-- url     : https://prove2.me/submissions/dfaee096-d121-4000-ba88-3769c25244c3

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
theorem _root_.solution (σ : L ≃ₐ[K] L) (y : CompletionsOver L v) (u : PlacesOver L v) :
    piGal v σ y u = galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u) (y (σ⁻¹ • u)) := rfl
end GroundTheory.Global.SemiLocal
