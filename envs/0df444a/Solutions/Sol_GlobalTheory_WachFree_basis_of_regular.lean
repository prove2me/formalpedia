-- Prove2me | solution 1 for GlobalTheory.WachFree.basis_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:38.512505+00:00
-- url     : https://prove2.me/submissions/af5dc8e5-40d0-4eaa-9c3c-fef92892357e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemXSmulOfProjective
import Theorems.Thm_GlobalTheory_WachFree_free_of_regular
import Theorems.Thm_GlobalTheory_WachFree_basis_of_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open GlobalTheory GlobalTheory.WachFree
namespace GlobalTheory.WachFree
theorem _root_.solution {ι O N E D : Type} [Finite ι] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup N] [Module (ι → O⟦X⟧) N] [Module.Finite (ι → O⟦X⟧) N]
    [CommRing E] [Algebra (ι → O⟦X⟧) E]
    (hE : Function.Injective (algebraMap (ι → O⟦X⟧) E)) [AddCommGroup D] [Module E D]
    [Module (ι → O⟦X⟧) D] [IsScalarTower (ι → O⟦X⟧) E D] [Module.Free E D]
    (f : N →ₗ[ι → O⟦X⟧] D) (hf : IsBaseChange E f) (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular N (fun _ => X : ι → O⟦X⟧))
    (h : ∀ x y : N, (fun _ => C c : ι → O⟦X⟧) • x = (fun _ => X : ι → O⟦X⟧) • y →
      ∃ z : N, x = (fun _ => X : ι → O⟦X⟧) • z) :
    Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → O⟦X⟧) N) := by
  letI : Module O⟦X⟧ N := Module.compHom _ (algebraMap O⟦X⟧ (ι → O⟦X⟧))
  haveI : IsScalarTower O⟦X⟧ (ι → O⟦X⟧) N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O⟦X⟧ N := Module.Finite.trans (ι → O⟦X⟧) _
  haveI : Module.Free O⟦X⟧ N := free_of_regular c hc hc' hX h
  exact basis_of_baseChange hE f hf
end GlobalTheory.WachFree
