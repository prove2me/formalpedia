-- Prove2me | solution 1 for GlobalTheory.FontCmp.letter_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:05:30.907317+00:00
-- url     : https://prove2.me/submissions/1ede59dd-57db-45ab-bd47-e652eec48f86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable (LL : Type) [Field LL] [Algebra Qp LL]
namespace GlobalTheory.FontCmp
theorem _root_.solution : CrystallineSubrepresentation.LetterDim PD LL ↔ TensorMultiplication.LetterDim PD LL := by
  refine forall_congr' fun _ => forall_congr' fun V => forall₄_congr fun _ _ _ _ =>
    forall₃_congr fun _ ρ _ => forall_congr' fun τ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · haveI : Subsingleton V := Module.finrank_zero_iff.1 h0
    infer_instance
  · exact Module.finite_of_finrank_pos (h ▸ h0)
end GlobalTheory.FontCmp
