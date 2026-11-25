-- Prove2me | solution 1 for GlobalTheory.Mass.OrbFib.encard_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:57.128515+00:00
-- url     : https://prove2.me/submissions/8021c878-a4f1-415c-8f60-b9753e30df7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres
import Theorems.Thm_GlobalTheory_Mass_OrbFib_mem_orbit_out

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
theorem _root_.solution (X : Set α) (hX : _root_.GlobalTheory.Mass.Stable G X)
    (S : Set α) :
    (((X ∩ S).encard : ℕ∞) : ℝ≥0∞) =
      ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        (((MulAction.orbit G (Quotient.out q.1) ∩ S).encard : ℕ∞) : ℝ≥0∞) := by
  have hmem : ∀ (q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X}) (a : α),
      a ∈ MulAction.orbit G (Quotient.out q.1) → a ∈ X := by
    rintro q a ⟨g, rfl⟩
    exact hX g _ q.2
  have h1 : ∀ T : Set α, ((T.encard : ℕ∞) : ℝ≥0∞) =
      ∑' a : α, T.indicator (fun _ => (1 : ℝ≥0∞)) a := by
    intro T
    rw [← ENNReal.tsum_set_one]
    exact tsum_subtype T (fun _ => (1 : ℝ≥0∞))
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  by_cases haS : a ∈ S
  · by_cases haX : a ∈ X
    · have hq0 : Quotient.out (Quotient.mk (MulAction.orbitRel G α) a) ∈ X := by
        obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel G α) a
        rw [← hg]
        exact hX g a haX
      rw [Set.indicator_of_mem (show a ∈ X ∩ S from ⟨haX, haS⟩), tsum_eq_single
        (⟨Quotient.mk _ a, hq0⟩ : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X})]
      · rw [Set.indicator_of_mem]
        exact ⟨(_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out _ a).2 rfl, haS⟩
      · intro q hq
        rw [Set.indicator_of_notMem]
        rintro ⟨h, -⟩
        exact hq (Subtype.ext ((_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out _ a).1 h).symm)
    · rw [Set.indicator_of_notMem (fun h : a ∈ X ∩ S => haX h.1)]
      symm
      refine ENNReal.tsum_eq_zero.2 fun q => ?_
      rw [Set.indicator_of_notMem]
      rintro ⟨h, -⟩
      exact haX (hmem q a h)
  · rw [Set.indicator_of_notMem (fun h : a ∈ X ∩ S => haS h.2)]
    symm
    refine ENNReal.tsum_eq_zero.2 fun q => ?_
    rw [Set.indicator_of_notMem]
    rintro ⟨-, h⟩
    exact haS h
end _root_.GlobalTheory.Mass.OrbFib
end GlobalTheory.Mass.OrbFib
