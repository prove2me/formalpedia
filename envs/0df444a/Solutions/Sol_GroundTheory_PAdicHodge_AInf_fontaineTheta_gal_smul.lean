-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_gal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:24:33.702122+00:00
-- url     : https://prove2.me/submissions/c98446be-94c2-4367-973a-7c8e62d59d2c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_map
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_gal_smul_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    ((WittVector.fontaineTheta (normInteger ℂ_[p]) p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((WittVector.fontaineTheta (normInteger ℂ_[p]) p x : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [gal_smul_def, galMap, fontaineTheta_map, coe_integerMap]
  rfl
end GroundTheory.PAdicHodge.AInf
