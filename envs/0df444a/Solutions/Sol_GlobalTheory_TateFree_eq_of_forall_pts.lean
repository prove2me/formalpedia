-- Prove2me | solution 1 for GlobalTheory.TateFree.eq_of_forall_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:56.135851+00:00
-- url     : https://prove2.me/submissions/5f250a6b-81b3-444a-bc14-de77716aed69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_TateFree_comp_ofId_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree
variable (O C A : Type) [CommRing O] [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
  [CommRing A]
variable [IsAlgClosed C] [CharZero C] [HopfAlgebra O A] [Module.Finite O A]
include C
namespace GlobalTheory.TateFree
theorem _root_.solution [Module.Flat O A] {a b : A} (h : ∀ x : A →ₐ[O] O, x a = x b) :
    a = b := by
  have := etale_of_hopfAlgebra C (C ⊗[O] A)
  have hi : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[O] C ⊗[O] A) :=
    Algebra.TensorProduct.includeRight_injective (IsIntegralClosure.algebraMap_injective O O C)
  refine hi ((Algebra.FormallyEtale.equivPiOfIsSepClosed C (C ⊗[O] A)).injective
    (funext fun q => ?_))
  let χ : C ⊗[O] A →ₐ[C] C := (Pi.evalAlgHom C (fun _ => C) q).comp
    (Algebra.FormallyEtale.equivPiOfIsSepClosed C (C ⊗[O] A) : _ →ₐ[C] _)
  obtain ⟨φ, hφ⟩ := (comp_ofId_bijective O C A).2 ((AlgHom.liftEquiv O C A C).symm χ)
  exact (DFunLike.congr_fun hφ a).symm.trans
    ((congrArg (Algebra.ofId O C) (h φ)).trans (DFunLike.congr_fun hφ b))
end GlobalTheory.TateFree
