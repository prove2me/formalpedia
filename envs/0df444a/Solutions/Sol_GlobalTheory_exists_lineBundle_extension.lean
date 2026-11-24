-- Prove2me | solution 1 for GlobalTheory.exists_lineBundle_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:49.451813+00:00
-- url     : https://prove2.me/submissions/9b53bf84-59b1-4f9c-82d6-28e54f330e35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_compatible_cover
import Theorems.Thm_GlobalTheory_ExtendLineBundle_unitVal_res
import Theorems.Thm_GlobalTheory_ExtendLineBundle_unit_ext
import Theorems.Thm_GlobalTheory_ExtendLineBundle_unitVal_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_unit
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_image_unit
import Theorems.Thm_GlobalTheory_ExtendLineBundle_mem_image_inf
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_equations
import Theorems.Thm_GlobalTheory_ExtendLineBundle_isGen_of_equations
import Theorems.Thm_GlobalTheory_ExtendLineBundle_imageVal_pull

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
open GlobalTheory
open ExtendLineBundle
namespace GlobalTheory
theorem _root_.solution (X Y : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] (j : Y ⟶ X) (hj : IsOpenImmersion j)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (L : LB Y) (hL : L.IsLB) :
    ∃ L' : LB X, L'.IsLB ∧ ∃ φ : LB.Iso (L'.pull j) L, φ.IsGen := by
  have : IsNoetherian X := {}
  obtain ⟨f, hf⟩ := exists_equations j L hL
  obtain ⟨T, h₀, hT, hc⟩ := exists_compatible_cover hX
    (T₀ := Set.range fun i => (j ''ᵁ L.U i, f i)) (by
      rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩ y hi hk
      rw [← hf i k (genericPoint_mem hi) (genericPoint_mem hk)]
      exact unitVal_mem (mem_image_inf j hi hk) _)
  choose g hg using fun p q : T => exists_unit (U := p.1.1 ⊓ q.1.1) (t := p.1.2 / q.1.2)
    fun y hy => hT _ p.2 _ q.2 y hy.1 hy.2
  let L' : LB X := ⟨T, fun p => p.1.1, g⟩
  choose s hs using fun p : L.ι × (PUnit → T) => exists_image_unit j
    (V := L.U p.1 ⊓ LB.wchart L' (fun _ => j) p.2) (t := f p.1 / (p.2 ⟨⟩).1.2) fun y hy =>
      hT _ (h₀ ⟨p.1, rfl⟩) _ (p.2 ⟨⟩).2 (j y) (j.apply_mem_image_iff.2 hy.1)
        (LB.wchart_le L' (fun _ => j) p.2 ⟨⟩ hy.2)
  refine ⟨L', ⟨?_, fun p => unit_ext fun h => ?_, fun p q r => unit_ext fun h => ?_⟩,
    ⟨s⟩, isGen_of_equations j L (L'.pull j) f (fun p => (p ⟨⟩).1.2) hf (fun p q hp hq => ?_) s hs⟩
  · refine top_unique fun x _ => ?_
    obtain ⟨p, hp, hx⟩ := hc x
    exact Opens.mem_iSup.2 ⟨⟨p, hp⟩, hx⟩
  · rw [unitVal_res _ h, map_one]
    exact (hg p p ⟨h, h⟩).trans (div_self' _)
  · rw [map_mul, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h]
    exact (congrArg₂ (· * ·) (hg p q h.1) (hg q r ⟨h.1.2, h.2⟩)).trans
      ((div_mul_div_cancel _ _ _).trans (hg p r ⟨h.1.1, h.2⟩).symm)
  · have hw := mem_image_inf j hp hq
    refine (imageVal_pull j L' p q hw).trans (hg (p ⟨⟩) (q ⟨⟩) ?_)
    obtain ⟨y, hy, e⟩ := hw
    rw [← e]
    exact ⟨LB.wchart_le L' (fun _ => j) p ⟨⟩ hy.1, LB.wchart_le L' (fun _ => j) q ⟨⟩ hy.2⟩
end GlobalTheory
