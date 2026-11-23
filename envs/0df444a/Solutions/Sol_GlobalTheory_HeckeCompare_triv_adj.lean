-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.triv_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:33.918124+00:00
-- url     : https://prove2.me/submissions/57ff9487-a721-4f16-9dff-e45237c6335b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_iff
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_adj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
  (I : TateIso D k Q (fun a x => ρ a x) e)
variable (hu : Uniq e)
include hu
include I
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1) (c : 𝓞 E) :
    e n (ρ c x) y 1 ↔ e n x (ρ (H.bar c) y) 1 := by
  obtain ⟨a, rfl⟩ := (I.onto n hn _).1 hx
  obtain ⟨b, rfl⟩ := (I.onto n hn _).1 hy
  rw [← I.lin n c a, ← I.lin n (H.bar c) b, triv_iff I hu hn, triv_iff I hu hn, D.adj]
end GlobalTheory.HeckeCompare
