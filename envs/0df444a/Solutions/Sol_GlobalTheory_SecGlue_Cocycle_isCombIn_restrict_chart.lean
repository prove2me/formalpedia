-- Prove2me | solution 1 for GlobalTheory.SecGlue.Cocycle.isCombIn_restrict_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:42.691712+00:00
-- url     : https://prove2.me/submissions/e52b9eb0-f6d7-4e44-b607-3c5930db09c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsAgreeOfCocycle
import Theorems.Thm_GlobalTheory_SecGlue_Cocycle_spMap_comp_spMap
import Theorems.Thm_GlobalTheory_SecGlue_isCombIn_spMap_comp
import Theorems.Thm_GlobalTheory_T_isAffineCombination_independent_of_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Cocycle
namespace GlobalTheory.SecGlue.Cocycle
theorem _root_.solution {Y : Scheme.{0}} {V V' : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') {S T S' : Type} [CommRing S] [CommRing T] [CommRing S']
    (q : S →+* T) (hq : Function.Surjective q) (h2 : RingHom.ker q ^ 2 = ⊥) (g : S →+* S')
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (hw : ∀ i, spMap q ≫ w i = spMap q ≫ u) (hC : IsCombIn V u c w a)
    (hu : (spMap g ≫ u) ⁻¹ᵁ V' = ⊤) :
    IsCombIn V' (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  let J : Ideal S' := (RingHom.ker q).map g
  have hle : RingHom.ker q ≤ RingHom.ker ((Ideal.Quotient.mk J).comp g) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem g hx
  let g' : T →+* S' ⧸ J := RingHom.liftOfSurjective q hq ⟨(Ideal.Quotient.mk J).comp g, hle⟩
  have hg' : g'.comp q = (Ideal.Quotient.mk J).comp g := RingHom.liftOfSurjective_comp q hq _
  refine GlobalTheory.T.isAffineCombination_independent_of_chart Y V V' hV hV' S' (S' ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    ?_ ι _ _ _ _ (fun i => ?_) (isCombIn_spMap_comp Y V S S' g ι u c w a hC) hu
  · rw [Ideal.mk_ker, ← Ideal.map_pow, h2, Ideal.map_bot]
  · rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, ← hg', ← spMap_comp_spMap,
      Category.assoc, Category.assoc, hw i]
end GlobalTheory.SecGlue.Cocycle
