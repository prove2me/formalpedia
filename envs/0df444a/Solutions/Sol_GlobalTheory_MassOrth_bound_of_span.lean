-- Prove2me | solution 1 for GlobalTheory.MassOrth.bound_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:52.546944+00:00
-- url     : https://prove2.me/submissions/640ca4d7-be18-436a-8318-faabe751ad38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
namespace GlobalTheory.MassOrth
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (T : Set V) (m : Γ)
    (hT : ∀ x ∈ T, ∀ y ∈ T, v (h x y) ≤ m) :
    ∀ x ∈ Submodule.span (biInt v) T, ∀ y ∈ Submodule.span (biInt v) T, v (h x y) ≤ m := by
  have h1 : ∀ x ∈ T, ∀ y ∈ Submodule.span (biInt v) T, v (h x y) ≤ m := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hT x hx y hy
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact v.map_add_le ha hb
    | smul r a _ ha =>
      rw [Subring.smul_def, map_smul, smul_eq_mul, map_mul]
      exact (mul_le_mul' r.2.1 ha).trans (by simp)
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx => exact h1 x hx y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact v.map_add_le ha hb
  | smul r a _ ha =>
    rw [Subring.smul_def, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul]
    exact (mul_le_mul' r.2.2 ha).trans (by simp)
end GlobalTheory.MassOrth
