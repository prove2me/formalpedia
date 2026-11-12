-- Prove2me | solution 1 for OAI.CubicEisenstein.onceRamified_row_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:46:38.211877+00:00
-- url     : https://prove2.me/submissions/7290e315-6b69-46c0-9a40-b1ef7d78918e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Theorems.Thm_OAI_CubicEisenstein_inverse_cosetCharacter_eq_row_symbol
import Theorems.Thm_OAI_CubicEisenstein_primitiveRowEquiv_symm_row
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_congr
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_reciprocity


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)
namespace OAI.CubicEisenstein
theorem _root_.solution (u:Eisˣ) (p:OnceRamifiedData) :
    (cosetCharacter (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))⁻¹=
      eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
        eisEmbedding (symbol p.2.2.val.val p.2.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val))
    p.2.2.val.val)=_
  have hh : symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val)) p.2.2.val.val=
      symbol ((onceCuspScale u*omega^p.1.val)*p.2.1.val) p.2.2.val.val :=
    symbol_congr ⟨-onceCuspScale u,by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.2.val),
    symbol_reciprocity p.2.1.val p.2.2.val.val (primaryLower_ne_zero p.2.1)
      (primaryLower_ne_zero p.2.2.val) (primaryLower_primary p.2.1)
        (primaryLower_primary p.2.2.val),map_mul]
end OAI.CubicEisenstein
