-- Prove2me | solution 1 for GroundTheory.PAdicHodge.integerTiltHom_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:02.841005+00:00
-- url     : https://prove2.me/submissions/f23664cd-c293-4110-8a52-8a6904312518

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois

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
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭) (σ τ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖)
    (hτ : ∀ x : N, ‖((τ x : N) : C♭)‖ = ‖(x : C♭)‖)
    (hστ : ∀ x : N, ‖(((σ.comp τ) x : N) : C♭)‖ = ‖(x : C♭)‖) :
    integerTiltHom N (σ.comp τ) hστ = (integerTiltHom N σ hσ).comp (integerTiltHom N τ hτ) := by
  ext a
  apply IsFractionRing.injective 𝒪C♭ C♭
  rw [algebraMap_integerTiltHom, RingHom.comp_apply, algebraMap_integerTiltHom]
  have : (⟨algebraMap 𝒪C♭ C♭ (integerTiltHom N τ hτ a : 𝒪C♭), (integerTiltHom N τ hτ a).2⟩ :
      N) = τ ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ := Subtype.ext (algebraMap_integerTiltHom N τ hτ a)
  rw [this]
  rfl
end GroundTheory.PAdicHodge
