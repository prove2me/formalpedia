-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.support_annihilatorIdealSheaf_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:42.560439+00:00
-- url     : https://prove2.me/submissions/2c281570-f9b0-484d-96f8-42cebaf73438

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Support
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Annihilator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (F : X.Modules) (hF : IsCoherent F) {T : Set X}
    (hT : IsClosed T) (hFT : Scheme.Modules.SupportedIn F T) :
    ((annihilatorIdealSheaf F hF).support : Set X) ⊆ T := by
  intro x hx
  by_contra hxT
  have := hF.1
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  have := hF.2 U U.2
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le (V := V) ⟨x, hxT⟩ hxU
  obtain ⟨E, hE⟩ := exists_pow_mul_mem_annihilatorIdeal F U.2 f 1 (fun m =>
    hFT _ (Set.disjoint_left.2 fun y hy hyT => hfV hy hyT) _)
  rw [mul_one] at hE
  have hE' : f ^ (E + 1) ∈ (annihilatorIdealSheaf F hF).ideal U := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hE
  have hx' : x ∈ (annihilatorIdealSheaf F hF).support := hx
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (show x ∈ U.1 from hxU),
    Scheme.mem_zeroLocus_iff] at hx'
  exact hx' _ hE' (by rwa [Scheme.basicOpen_pow _ _ (Nat.succ_pos E)])
end GroundTheory.Arith.SchemeCoh
