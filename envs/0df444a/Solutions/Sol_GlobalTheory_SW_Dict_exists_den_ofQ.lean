-- Prove2me | solution 1 for GlobalTheory.SW.Dict.exists_den_ofQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:53.823026+00:00
-- url     : https://prove2.me/submissions/f528a020-5db7-4fc3-bdef-0658bd09cacc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution : ∃ D : ℕ, 0 < D ∧
    ∀ m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ, _root_.GlobalTheory.SW.IntM m →
    _root_.GlobalTheory.SW.IntM (D • _root_.GlobalTheory.SW.Dict.ofQEquiv E n N m) := by
  obtain ⟨D, hD, hb⟩ := _root_.GlobalTheory.SW.Dict.exists_den (Module.finBasis ℚ E)
  refine ⟨D, hD, fun m hm k a => ?_⟩
  show IsIntegral ℤ (D • ∑ j, m k (a, j) • Module.finBasis ℚ E j)
  rw [Finset.smul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [smul_comm, Algebra.smul_def]
  exact ((hm k (a, j)).map (IsScalarTower.toAlgHom ℤ ℚ E)).mul (hb j)
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
