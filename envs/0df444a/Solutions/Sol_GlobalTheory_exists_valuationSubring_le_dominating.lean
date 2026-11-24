-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_le_dominating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:46.262186+00:00
-- url     : https://prove2.me/submissions/594aa125-f49b-49f7-8804-fbaf53cb4c3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
import Theorems.Thm_GlobalTheory_mem_compositeValuationSubring
import Theorems.Thm_GlobalTheory_compositeValuationSubring_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {O L : Type*} [CommRing O] [IsLocalRing O]
    [Field L] (g : O →+* L) (W : ValuationSubring L) (hg : ∀ x, g x ∈ W) :
    ∃ W' : ValuationSubring L, W' ≤ W ∧ (∀ x : O, g x ∈ W') ∧
      ∀ x ∈ maximalIdeal O, g x ∈ W'.nonunits := by
  let g' : O →+* W := g.codRestrict W.toSubring hg
  let f : O →+* ResidueField W := (residue W).comp g'
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨compositeValuationSubring W V, compositeValuationSubring_le W V, fun x =>
    (mem_compositeValuationSubring W V _).2 ⟨hg x, hV x⟩, fun x hx => ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_or]
  rcases eq_or_ne (g x) 0 with h0 | h0
  · exact Or.inl h0
  refine Or.inr fun hinv => ?_
  obtain ⟨h, hres⟩ := (mem_compositeValuationSubring W V _).1 hinv
  have hmul : f x * residue W ⟨(g x)⁻¹, h⟩ = 1 := by
    change residue W (g' x) * _ = 1
    rw [← map_mul, ← map_one (residue W)]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ h0)
  have hu : IsUnit (f.codRestrict V.toSubring hV x) :=
    isUnit_iff_exists_inv.2 ⟨⟨_, hres⟩, Subtype.ext hmul⟩
  exact (mem_maximalIdeal x).1 hx (hloc.1 x hu)
end GlobalTheory
