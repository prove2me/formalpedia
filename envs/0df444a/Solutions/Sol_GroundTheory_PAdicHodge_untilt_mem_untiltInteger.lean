-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untilt_mem_untiltInteger
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:06:51.606195+00:00
-- url     : https://prove2.me/submissions/4499cf1b-83a9-49af-b8ce-85584797a1dd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField

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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {N : IntermediateField K♭ C♭} {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) :
    PreTilt.untilt a ∈ untiltInteger K C p N :=
  ⟨WittVector.teichmuller p ⟨a, ha⟩, by
    rw [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
    rfl⟩
end GroundTheory.PAdicHodge
