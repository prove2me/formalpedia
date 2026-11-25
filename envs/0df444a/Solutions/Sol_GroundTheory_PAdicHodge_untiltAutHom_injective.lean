-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltAutHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:56.405818+00:00
-- url     : https://prove2.me/submissions/e32bf9fc-98c5-427f-a5b8-f9052e093d2f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Theorems.Thm_GroundTheory_PAdicHodge_untiltPreTiltAut_eq_id

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
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    Function.Injective (untiltAutHom (K := K) (C := C) (p := p) N) := by
  refine (injective_iff_map_eq_one _).2 fun σ h => ?_
  have h' : untiltAut N σ = 1 := h

  have hint : ∀ a : integerTilt K C p N,
      integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) a = a := by
    intro a
    obtain ⟨b, rfl⟩ := (preTiltUntiltEquiv N).surjective a
    rw [← preTiltUntiltEquiv_untiltPreTiltAut, untiltPreTiltAut_eq_id N σ h' b]
  have key : ∀ x : N, ‖(x : C♭)‖ ≤ 1 → σ x = x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := exists_algebraMap_eq_of_mem (p := p) x.2 hx
    apply Subtype.ext
    have := algebraMap_integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) ⟨a, ha⟩
    rw [hint] at this
    have hx' : (⟨algebraMap 𝒪C♭ C♭ a, ha⟩ : N) = x := Subtype.ext hax
    rw [hx'] at this
    exact this.symm.trans hax
  ext x
  rcases le_or_gt ‖(x : C♭)‖ 1 with hx | hx
  · exact congrArg Subtype.val (key x hx)
  · have hx0 : x ≠ 0 := by
      rintro rfl; norm_num at hx
    have := key x⁻¹ (by
      rw [IntermediateField.coe_inv, norm_inv]; exact inv_le_one_of_one_le₀ hx.le)
    rw [map_inv₀] at this
    exact congrArg Subtype.val (inv_injective this)
end GroundTheory.PAdicHodge
