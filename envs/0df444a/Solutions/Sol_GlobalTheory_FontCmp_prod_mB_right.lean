-- Prove2me | solution 1 for GlobalTheory.FontCmp.prod_mB_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:10.284416+00:00
-- url     : https://prove2.me/submissions/2328fb87-b72b-4e46-a42f-4963f7f49636

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineSubrepresentation_prodB_tmul


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
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
namespace GlobalTheory.FontCmp
theorem _root_.solution (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] mB LL b y) = mB LL b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_left_comm]
end GlobalTheory.FontCmp
