-- Prove2me | solution 1 for GlobalTheory.existsUnique_sec_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:10.12528+00:00
-- url     : https://prove2.me/submissions/1cc85a6a-16ae-4a6d-bae0-40a02a5267e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_bijective_appLE_of_eq
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
      (inf_le_inf (hU i).le (hU j).le)).hom (L.g (e i) (e j)).val) (s : L'.Sec) :
    ∃! t : L.Sec, ∀ j, (f.appLE (L.U (e j)) (L'.U j) (hU j).le).hom (t.f (e j)) = s.f j := by
  have hb (j) := bijective_appLE_of_eq f (hU j) (hf _)
  choose a ha using fun j ↦ (hb j).2 (s.f j)
  let t : ∀ i, Γ(X, L.U i) := e.piCongrLeft (fun i ↦ Γ(X, L.U i)) a
  have ht (j) : t (e j) = a j := e.piCongrLeft_apply_apply (fun i ↦ Γ(X, L.U i)) a j
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun j ↦ by rw [← ha, ← ht], fun t' ht' ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    apply (bijective_appLE_of_eq f (V := L.U (e i) ⊓ L.U (e j)) (W := L'.U i ⊓ L'.U j)
      (by rw [hU, hU]; rfl) (hf _)).1
    have := s.compat i j
    rw [← ha, ← ha, res_appLE_apply, res_appLE_apply, hg] at this
    rw [map_mul, appLE_res_apply, appLE_res_apply, ht, ht]
    exact this
  · cases t' with | mk t' _ => ?_
    congr 1
    funext i
    obtain ⟨i, rfl⟩ := e.surjective i
    exact (hb i).1 ((ht' i).trans (by rw [ht, ha]))
end GlobalTheory
