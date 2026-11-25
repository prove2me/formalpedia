-- Prove2me | solution 1 for GroundTheory.PAdicHodge.algebraMap_mem_tiltIntermediateField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:08.044506+00:00
-- url     : https://prove2.me/submissions/8278f264-3143-446b-b903-dca35078700e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt_iterate
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_preTilt_ext
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_iterate_succ_pow
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
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
local notation "𝒪C♭" => PreTilt (normInteger C) p
variable (F : IntermediateField K C) [IsPerfectoidField F p]
local notation "F♭" => Tilt F NormedField.valuation (normInteger F) normInteger_integers p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a : 𝒪C♭}
    (ha : ∀ n, ((PreTilt.untilt ((frobeniusEquiv 𝒪C♭ p).symm^[n] a) : normInteger C) : C) ∈ F) :
    algebraMap 𝒪C♭ C♭ a ∈ tiltIntermediateField p F := by
  let y : ℕ → normInteger F := fun n =>
    ⟨⟨_, ha n⟩, mem_normInteger.2 (mem_normInteger.1
      (PreTilt.untilt ((frobeniusEquiv 𝒪C♭ p).symm^[n] a)).2)⟩
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => by
    apply Subtype.ext; apply Subtype.ext
    change ((PreTilt.untilt ((frobeniusEquiv 𝒪C♭ p).symm^[n + 1] a) : normInteger C) : C) ^ p = _
    rw [← SubmonoidClass.coe_pow, IsPerfectoidField.untilt_iterate_succ_pow]
  refine ⟨algebraMap _ _ (IsPerfectoidField.ofCompatible p y hy), ?_⟩
  rw [tiltInclusion, tiltMap_algebraMap]
  congr 1
  refine IsPerfectoidField.preTilt_ext p fun n => ?_
  change Perfection.coeff (ModP (normInteger C) p) p n (preTiltMap p _ _ _) = _
  rw [coeff_preTiltMap]
  change modPMap _ _ (Ideal.Quotient.mk _ (y n)) = _
  rw [modPMap_mk, ← IsPerfectoidField.mk_untilt_iterate]
  rfl
end GroundTheory.PAdicHodge
