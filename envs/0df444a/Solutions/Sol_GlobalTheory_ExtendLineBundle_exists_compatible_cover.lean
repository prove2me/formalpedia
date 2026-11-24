-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_compatible_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:07.293879+00:00
-- url     : https://prove2.me/submissions/b27cdc43-c4ab-4901-b66f-198c4f0a1a8d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_local_equation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution [NoetherianSpace X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {T₀ : Set (X.Opens × X.functionFieldˣ)} (h₀ : Compatible T₀) :
    ∃ T, T₀ ⊆ T ∧ Compatible T ∧ ∀ x, ∃ p ∈ T, x ∈ p.1 := by
  obtain ⟨T, h₁, hT⟩ := zorn_subset_nonempty {T : Set (X.Opens × X.functionFieldˣ) | Compatible T}
    (fun c hc hch _ => ⟨⋃₀ c, fun p ⟨s, hs, hp⟩ q ⟨s', hs', hq⟩ => by
      rcases hch.total hs hs' with h | h
      exacts [hc hs' p (h hp) q hq, hc hs p hp q (h hq)], fun s hs => Set.subset_sUnion_of_mem hs⟩)
    T₀ h₀
  refine ⟨T, h₁, hT.prop, fun x => ?_⟩
  have := hX x
  obtain ⟨W, h, hx, hW⟩ := exists_local_equation hT.prop x
  refine ⟨(W, h), hT.2 (y := insert (W, h) T) ?_ (Set.subset_insert _ _) (Set.mem_insert _ _), hx⟩
  rintro p (rfl | hp) q (rfl | hq) y hyp hyq
  · rw [div_self']
    exact one_mem _
  · exact hW q hq y hyp hyq
  · rw [← inv_div]
    exact inv_mem (hW p hp y hyq hyp)
  · exact hT.prop p hp q hq y hyp hyq
end GlobalTheory.ExtendLineBundle
