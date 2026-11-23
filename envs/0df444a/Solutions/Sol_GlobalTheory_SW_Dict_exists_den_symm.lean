-- Prove2me | solution 1 for GlobalTheory.SW.Dict.exists_den_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:07.094871+00:00
-- url     : https://prove2.me/submissions/bd29d4c1-2f5e-46d8-a718-5a7e9085eccd

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
    ∀ x : Matrix (Fin n) (Fin N) E, _root_.GlobalTheory.SW.IntM x →
    _root_.GlobalTheory.SW.IntM (D • (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).symm x) := by
  obtain ⟨D, hD, hc⟩ := _root_.GlobalTheory.SW.Dict.exists_den
    (fun p : _ × Fin (Module.finrank ℚ E) => (Module.finBasis ℚ E).repr (integralBasis E p.1) p.2)
  have key : ∀ y ∈ Submodule.span ℤ (Set.range (integralBasis E)),
      ∀ j, IsIntegral ℤ (D • (Module.finBasis ℚ E).repr y j) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact fun j => hc (i, j)
    | zero => intro j; simpa using isIntegral_zero
    | add y z _ _ hy hz =>
      intro j
      simpa [smul_add] using (hy j).add (hz j)
    | smul a y _ hy =>
      intro j
      rw [map_zsmul, Finsupp.smul_apply, smul_comm]
      simpa [zsmul_eq_mul] using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := a)).mul (hy j)
  refine ⟨D, hD, fun x hx k p => ?_⟩
  show IsIntegral ℤ (D • (Module.finBasis ℚ E).repr (x k p.1) p.2)
  exact key _ ((mem_span_integralBasis E).mpr ⟨⟨x k p.1, hx k p.1⟩, rfl⟩) p.2
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
