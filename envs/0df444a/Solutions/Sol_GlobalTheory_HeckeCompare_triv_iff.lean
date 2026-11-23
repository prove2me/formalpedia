-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.triv_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:08.089638+00:00
-- url     : https://prove2.me/submissions/189e875e-8d92-4164-83a5-6315a64c2e6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_ev_pow

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
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {n : ℕ} (hn : 0 < n) (a b : D.La) : e n (I.ev n a) (I.ev n b) 1 ↔ (n : ℤ) ∣ D.EF a b := by
  rw [← (I.ζ_prim n hn).zpow_eq_one_iff_dvd]
  exact ⟨fun h => hu n _ _ _ _ hn (ev_pow I hn a) (ev_pow I hn b) (I.isom n hn a b) h,
    fun h => h ▸ I.isom n hn a b⟩
end GlobalTheory.HeckeCompare
