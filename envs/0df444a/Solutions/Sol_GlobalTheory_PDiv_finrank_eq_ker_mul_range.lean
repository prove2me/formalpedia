-- Prove2me | solution 1 for GlobalTheory.PDiv.finrank_eq_ker_mul_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:54.373873+00:00
-- url     : https://prove2.me/submissions/69ca46b2-f588-45f6-9ab6-5748ca18b997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_HopfShear_shear
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
import Theorems.Thm_GlobalTheory_finrank_eq_mul_of_basis_tensor_self


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
open GlobalTheory GlobalTheory.PDiv
namespace GlobalTheory.PDiv
theorem _root_.solution (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    finrank k A = finrank k (A ⧸ kerIdeal f) *
      finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  exact GlobalTheory.finrank_eq_mul_of_basis_tensor_self k (AlgHom.range (f : B →ₐ[k] A)) A _ Subtype.val_injective
    ⟨((Module.finBasis k _).baseChange A).map e.symm⟩
end GlobalTheory.PDiv
