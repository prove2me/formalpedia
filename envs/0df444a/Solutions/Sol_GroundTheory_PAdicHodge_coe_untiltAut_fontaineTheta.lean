-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coe_untiltAut_fontaineTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:27.946022+00:00
-- url     : https://prove2.me/submissions/6e51d426-8492-42d3-9b4a-b3f219d317ee

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_subtype
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_untiltAut_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (u : WittVector p (integerTilt K C p N))
    (hu : ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) ∈ untiltField K C p N) :
    ((untiltAut N σ ⟨_, hu⟩ : untiltField K C p N) : C) =
      ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype
        (WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u)) :
        normInteger C) : C) := by
  have he : (⟨_, hu⟩ : untiltField K C p N) =
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
          (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) :
        normInteger (untiltField K C p N)) : untiltField K C p N) :=
    Subtype.ext (fontaineTheta_map_subtype N u)
  rw [he, untiltAut_coe, untiltIntegerHom_fontaineTheta, fontaineTheta_map_subtype,
    ← wittVector_map_comp, ← wittVector_map_comp]
  congr 3
  ext a
  simp [untiltPreTiltAut]
end GroundTheory.PAdicHodge
