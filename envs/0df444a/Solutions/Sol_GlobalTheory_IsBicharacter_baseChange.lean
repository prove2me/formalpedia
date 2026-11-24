-- Prove2me | solution 1 for GlobalTheory.IsBicharacter.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:51.476266+00:00
-- url     : https://prove2.me/submissions/7d2ec2af-58bf-4580-ab6e-478c49374972

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_pairingMap_pairingBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open CartierDual
variable {R : Type*} [CommSemiring R]
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}
variable (A : Type*) [CommSemiring A] [Algebra R A]
variable [Module.Finite R H] [Module.Projective R H] [Module.Finite R K] [Module.Projective R K]
namespace GlobalTheory
namespace IsBicharacter
theorem _root_.solution (hu : IsBicharacter R u) :
    IsBicharacter A (pairingBaseChange A u) := by
  refine (isBicharacter_iff_exists_bialgHom _).2
    ⟨(Bialgebra.TensorProduct.map (BialgHom.id A A) hu.toBialgHom).comp
      ((CartierDual.baseChange R A H).symm : _ →ₐc[A] _), fun Φ => ?_⟩
  obtain ⟨x, rfl⟩ := (CartierDual.baseChange R A H).surjective Φ
  refine Eq.trans ?_ (pairingMap_pairingBaseChange A u x).symm
  exact congrArg ((pairingMap R u).baseChange A)
    ((CartierDual.baseChange R A H).symm_apply_apply x)
end IsBicharacter
end GlobalTheory
