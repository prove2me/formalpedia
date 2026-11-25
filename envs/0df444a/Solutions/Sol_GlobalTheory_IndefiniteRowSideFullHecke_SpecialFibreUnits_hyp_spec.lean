-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.hyp_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:53.836499+00:00
-- url     : https://prove2.me/submissions/df791c0c-237e-4ba0-acc6-df5df4f4d3a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SpecialFibreUnits_linComb_g_one
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SpecialFibreUnits_normal_stalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Hyp (𝟙 (Spec (.of O))) (trivLB _) := by
  refine ⟨inferInstance, fun z => ?_, inferInstance, inferInstance, ?_, ⟨?_, ?_, ?_⟩,
    ⟨⟨fun _ => 1⟩, ?_⟩⟩
  · exact normal_stalk O z
  · have : ConnectedSpace (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) := inferInstance
    let e := pullback.snd (𝟙 (Spec (.of O))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    exact (Scheme.homeoOfIso (asIso e)).symm.surjective.connectedSpace
      (Scheme.homeoOfIso (asIso e)).symm.continuous
  · simp [trivLB]
  · intro i; exact map_one _
  · intro i j k
    change res _ 1 * res _ 1 = res _ 1
    simp
  · intro i j
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (linComb_g_one (trivLB _) (fun _ _ => rfl) _ _ i j) (map_one _)).trans (one_mul _)
end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
