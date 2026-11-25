-- Prove2me | solution 1 for GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:41.055296+00:00
-- url     : https://prove2.me/submissions/392c17b1-eeb2-4024-8db4-641297701f60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsCompletelyReducibleKroneckerOfSpanEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CompletelyReducibleToMatrixIffIsSemisimpleRepres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodOfIsIrreducibleAl
import Theorems.Thm_GlobalTheory_ClassFin_span_range_toMatrix_eq_top_of_isIrreducible
import Theorems.Thm_GlobalTheory_ClassFin_ss_range_toMatrix_iff_isSemisimpleRepresentation
import Theorems.Thm_GlobalTheory_T_isCompletelyReducible_kronecker_of_span_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsIrreducible → ρ'.IsIrreducible → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ h h'
  let b := Module.finBasis ℂ V
  let b' := Module.finBasis ℂ W
  have key := GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top _ _ G _ _ (span_range_toMatrix_eq_top_of_isIrreducible ρ b h)
    (span_range_toMatrix_eq_top_of_isIrreducible ρ' b' h')
  rw [← ss_range_toMatrix_iff_isSemisimpleRepresentation _ G _ _ (b.tensorProduct b')]
  convert key using 3 with g
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  rfl
end GlobalTheory.ClassFin
