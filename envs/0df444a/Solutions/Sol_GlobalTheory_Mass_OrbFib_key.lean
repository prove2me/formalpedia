-- Prove2me | solution 1 for GlobalTheory.Mass.OrbFib.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:30.991615+00:00
-- url     : https://prove2.me/submissions/dba01307-e8ca-470f-a7be-e6791f9959cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.OrbFib
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]
open NumberField Matrix
open scoped ENNReal Classical
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]
namespace GlobalTheory.Mass.OrbFib
namespace _root_.GlobalTheory.Mass.OrbFib
theorem _root_.solution (π : α → β)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : α) (k : G) :
    ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) =
      (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) *
        ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) := by
  have hkx : π (k • x) = k • π x := hπ k x
  have e1 : MulAction.stabilizer (MulAction.stabilizer G (k • π x)) (k • x) ≃
      MulAction.stabilizer G (k • x) :=
    { toFun := fun h => ⟨(h.1 : G), h.2⟩
      invFun := fun g => ⟨⟨g.1, by
          rw [MulAction.mem_stabilizer_iff, ← hkx, ← hπ,
            MulAction.mem_stabilizer_iff.1 g.2]⟩, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : MulAction.stabilizer G (k • x) ≃ MulAction.stabilizer G x := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact ((MulAction.stabilizer G x).equivMapOfInjective _
      (MulAut.conj k).injective).toEquiv.symm
  have e3 : MulAction.orbit (MulAction.stabilizer G (k • π x)) (k • x) =
      MulAction.orbit G x ∩ π ⁻¹' {k • π x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨(h : G) * k, ?_⟩, ?_⟩
      · show ((h : G) * k) • x = (h : G) • (k • x)
        exact mul_smul _ _ _
      · show π ((h : G) • (k • x)) = k • π x
        rw [hπ, hkx]
        exact h.2
    · rintro ⟨⟨g, rfl⟩, hz⟩
      have hz' : g • π x = k • π x := by rw [← hπ]; exact hz
      refine ⟨⟨g * k⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_smul, hz']
      · show (g * k⁻¹) • (k • x) = g • x
        rw [mul_smul, inv_smul_smul]
  have e4 : (MulAction.stabilizer G (k • π x) ⧸
      MulAction.stabilizer (MulAction.stabilizer G (k • π x)) (k • x)) ≃
      (MulAction.orbit G x ∩ π ⁻¹' {k • π x} : Set α) :=
    (MulAction.orbitEquivQuotientStabilizer _ (k • x)).symm.trans (Equiv.setCongr e3)
  have hcard : ENat.card (MulAction.stabilizer G (k • π x)) =
      (MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard *
        ENat.card (MulAction.stabilizer G x) := by
    rw [Set.encard, ← ENat.card_congr e4, ← ENat.card_congr (e1.trans e2), ← ENat.card_prod]
    exact ENat.card_congr Subgroup.groupEquivQuotientProdSubgroup
  rw [hcard]
  exact ENat.toENNReal_mul _ _
end _root_.GlobalTheory.Mass.OrbFib
end GlobalTheory.Mass.OrbFib
