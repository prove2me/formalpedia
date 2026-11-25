-- Prove2me | solution 1 for GlobalTheory.IsoLift.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:03.173295+00:00
-- url     : https://prove2.me/submissions/3b4271a8-6d77-42c9-9a31-b0f8f8447fdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsometryLift
import Theorems.Thm_GlobalTheory_IsoLift_cls_eq_iff_modN
import Theorems.Thm_GlobalTheory_SimLift_exists_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoLift
open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.IsoLift
theorem _root_.solution (n : ℕ+) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ e : LaMod D n ≃ₗ[𝓞 E] LaMod D n, ∀ a, e (cls D n a) = cls D n (f a) := by
  obtain ⟨g, hg⟩ := exists_inv D n.pos hf
  have hle : ∀ u : D.La →ₗ[𝓞 E] D.La, nLa D n ≤ (nLa D n).comap u := by
    intro u x hx
    obtain ⟨y, rfl⟩ := (mem_nLa D).mp hx
    exact (mem_nLa D).mpr ⟨u y, map_nsmul u _ y⟩
  refine ⟨LinearEquiv.ofLinear ((nLa D n).mapQ _ f (hle f)) ((nLa D n).mapQ _ g (hle g)) ?_ ?_,
    fun a => rfl⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (cls_eq_iff_modN D).mpr (hg a).2
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (cls_eq_iff_modN D).mpr (hg a).1
end GlobalTheory.IsoLift
