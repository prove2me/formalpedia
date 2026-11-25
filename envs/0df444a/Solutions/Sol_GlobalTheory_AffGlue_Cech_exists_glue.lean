-- Prove2me | solution 1 for GlobalTheory.AffGlue.Cech.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:17.539053+00:00
-- url     : https://prove2.me/submissions/c00f84e6-2234-46a7-95e7-c9f4dc48311a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineCoverSectionsGlue
import Theorems.Thm_GlobalTheory_AffGlue_Cech_eq_zero_of_small
import Theorems.Thm_GlobalTheory_AffGlue_Cech_exists_glue_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
open GlobalTheory GlobalTheory.AffGlue GlobalTheory.AffGlue.Cech
variable {T : Scheme.{0}}
namespace GlobalTheory.AffGlue.Cech
theorem _root_.solution {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V)
    {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V)
    (hc : V ≤ ⨆ i, W i) (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) :
    ∃ x : D.M V hV, ∀ i, D.ρ hV (hW i) (hWV i) x = m i := by
  obtain ⟨s, hs⟩ := hV.isCompact.elim_finite_subcover (fun i => (W i : Set T))
    (fun i => (W i).isOpen) (fun x hx => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
      exact Set.mem_iUnion.2 ⟨i, hi⟩)
  obtain ⟨x, hx⟩ := exists_glue_finset D hV W hW hWV hc m hm s
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_small D (hW i) (fun k : s => W k) (fun y hy => ?_) _ ?_
  · obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hs (hWV i hy))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk⟩, hyk⟩
  · rintro ⟨k, hk⟩ O hO h hOk
    rw [map_sub, D.ρ_ρ, hm i k O hO h hOk, ← hx k hk, D.ρ_ρ, sub_self]
end GlobalTheory.AffGlue.Cech
