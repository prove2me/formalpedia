-- Prove2me | solution 1 for GlobalTheory.existsUnique_gen_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:15:22.987813+00:00
-- url     : https://prove2.me/submissions/03b700fa-e027-4cfc-adf9-421fc989002f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_bijective_appLE_of_eq
import Theorems.Thm_GlobalTheory_existsUnique_sec_of_charts
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    {L : LB X} {L' : LB Y} (e : L'.ι ≃ L.ι) (hU : ∀ j, L'.U j = f ⁻¹ᵁ L.U (e j))
    (hg : ∀ i j, (L'.g i j).val = (f.appLE (L.U (e i) ⊓ L.U (e j)) (L'.U i ⊓ L'.U j)
      (inf_le_inf (hU i).le (hU j).le)).hom (L.g (e i) (e j)).val) (s : L'.Gen) (hs : s.IsGen) :
    ∃! t : L.Gen, t.IsGen ∧
      ∀ j, (f.appLE (L.U (e j)) (L'.U j) (hU j).le).hom (t.s (e j)).val = (s.s j).val := by
  obtain ⟨t, ht, hu⟩ := existsUnique_sec_of_charts f hf e hU hg
    ⟨fun j ↦ (s.s j).val, fun i j ↦ congrArg Units.val (hs i j)⟩
  have hunit (i) : IsUnit (t.f i) := by
    obtain ⟨i, rfl⟩ := e.surjective i
    have hb := bijective_appLE_of_eq f (hU i) (hf _)
    refine (MulEquiv.isUnit_map (RingEquiv.ofBijective _ hb)).mp ?_
    rw [RingEquiv.ofBijective_apply, ht]
    exact (s.s i).isUnit
  refine ⟨⟨fun i ↦ (hunit i).unit⟩, ⟨fun i j ↦ Units.ext (t.compat i j), ht⟩, ?_⟩
  rintro ⟨t'⟩ ⟨h1, h2⟩
  have := hu ⟨fun j ↦ (t' j).val, fun i j ↦ congrArg Units.val (h1 i j)⟩ h2
  congr 1
  funext i
  exact Units.ext (congrArg (fun z : L.Sec ↦ z.f i) this)
end GlobalTheory
