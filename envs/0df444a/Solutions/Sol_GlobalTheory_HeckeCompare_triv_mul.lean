-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.triv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:33.756382+00:00
-- url     : https://prove2.me/submissions/6348b762-e677-4fdc-bd2c-365a85fb0e8d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_iff

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) {x x' y : Q} (hx : x ^ n = 1) (hx' : x' ^ n = 1) (hy : y ^ n = 1)
    (h : e n x y 1) (h' : e n x' y 1) : e n (x * x') y 1 := by
  obtain ⟨a, rfl⟩ := (I.onto n hn _).1 hx
  obtain ⟨a', rfl⟩ := (I.onto n hn _).1 hx'
  obtain ⟨b, rfl⟩ := (I.onto n hn _).1 hy
  rw [triv_iff I hu hn] at h h'
  rw [← I.add, triv_iff I hu hn, map_add, LinearMap.add_apply]
  exact dvd_add h h'
end GlobalTheory.HeckeCompare
