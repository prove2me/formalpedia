-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.triv_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:32:12.402722+00:00
-- url     : https://prove2.me/submissions/9ccc932a-fa8f-411a-a432-10c6ab30e9fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_ev_nsmul
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
theorem _root_.solution {p : ℕ} (hp : 0 < p) {x y : Q} (hx : x ^ (p * p) = 1) (hy : y ^ p = 1) :
    e (p * p) x y 1 ↔ e p (x ^ p) y 1 := by
  have hq := Nat.mul_pos hp hp
  obtain ⟨a, rfl⟩ := (I.onto _ hq _).1 hx
  obtain ⟨b, rfl⟩ := (I.onto _ hp _).1 hy
  rw [I.tower p p hp hp, triv_iff I hu hp, ← I.tower p p hp hp b, ← ev_nsmul, triv_iff I hu hq, map_nsmul,
    nsmul_eq_mul, Nat.cast_mul, mul_dvd_mul_iff_left (Nat.cast_ne_zero.2 hp.ne')]
end GlobalTheory.HeckeCompare
