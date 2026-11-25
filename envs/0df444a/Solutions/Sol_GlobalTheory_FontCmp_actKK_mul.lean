-- Prove2me | solution 1 for GlobalTheory.FontCmp.actKK_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:53.647204+00:00
-- url     : https://prove2.me/submissions/bb3de2f4-1b00-4e36-a8d6-f8971ac8c996

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_mB_mul
import Theorems.Thm_GlobalTheory_FontCmp_actKK_tmul

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
theorem _root_.solution (τ : K₀ →ₐ[Qp] LL) (s t : K₀ ⊗[Qp] K₀) (x : V ⊗[Qp] B) :
    actKK LL V τ (s * t) x = actKK LL V τ s (actKK LL V τ t x) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [add_mul, map_add, LinearMap.add_apply, ha, hc]
  | tmul a c =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [mul_add, map_add, LinearMap.add_apply, ha, hc]
    | tmul a' c' => simp [actKK_tmul, mB_mul, smul_smul, mul_comm]
end GlobalTheory.FontCmp
