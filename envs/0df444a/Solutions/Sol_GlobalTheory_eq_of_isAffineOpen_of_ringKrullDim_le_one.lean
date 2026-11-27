-- Prove2me | solution 1 for GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:41:33.882809+00:00
-- url     : https://prove2.me/submissions/70b30520-9288-465d-8da5-ce55295cd7ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfIsAffineOpenOfRingKrullDimLeOne
import Theorems.Thm_GlobalTheory_isIso_of_isAffine_of_coheight_le_one
import Theorems.Thm_GlobalTheory_coheight_apply_of_isOpenImmersion
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (X : Scheme.{0}) [IsLocallyNoetherian X]
    [X.IsSeparated] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (V V' : X.Opens)
    (hV : IsAffineOpen V) (hle : V ≤ V')
    (h : ∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) : V' = V := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  refine le_antisymm (fun z hz ↦ ?_) hle
  obtain ⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V'.isOpen
  have hN' : IsAffineOpen N := hN
  have hNV' : IsAffineOpen (N ⊓ V) := hN'.inf hV
  have : IsAffine N := hN'
  have : IsAffine (N ⊓ V : X.Opens) := hNV'
  have hiso : IsIso (X.homOfLE (inf_le_left : N ⊓ V ≤ N)) := by
    refine isIso_of_isAffine_of_coheight_le_one _ fun x hx ↦ ?_
    have hx' : Order.coheight (Scheme.Opens.ι N x) ≤ 1 := by rwa [coheight_apply_of_isOpenImmersion]
    have hxV : Scheme.Opens.ι N x ∈ V := h _ (hNV x.2) ((ringKrullDim_stalk_le_one_iff _).mpr hx')
    exact ⟨⟨x.1, x.2, hxV⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  obtain ⟨y, hy⟩ := (X.homOfLE (inf_le_left : N ⊓ V ≤ N)).surjective ⟨z, hzN⟩
  have hyz : y.1 = z := (Scheme.homOfLE_apply _ y).symm.trans (congrArg Subtype.val hy)
  exact hyz ▸ y.2.2
end GlobalTheory
