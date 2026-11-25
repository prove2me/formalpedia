-- Prove2me | solution 1 for GlobalTheory.Mass.orbSum_eq_sum_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:07:56.939013+00:00
-- url     : https://prove2.me/submissions/6a901b3d-d0cc-41fc-a481-066eea7d5748

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumEqSumOrbitReps

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
open GlobalTheory GlobalTheory.Mass
open NumberField Matrix
open scoped ENNReal Classical
namespace GlobalTheory.Mass
namespace _root_.GlobalTheory.Mass
theorem _root_.solution : ∀ (G α : Type) [Group G] [MulAction G α]
    (X : Set α) (N : α → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → (∀ (g : G) x, N (g • x) = N x) →
    ∀ s : Finset α, (∀ x ∈ s, x ∈ X) → (∀ x ∈ X, ∃! y, y ∈ s ∧ ∃ g : G, g • y = x) →
    _root_.GlobalTheory.Mass.orbSum G X N =
      ∑ x ∈ s, ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
  intro G α _ _ X N hX hN s hs huniq
  have hX' : ∀ (g : G), ∀ x ∈ X, g • x ∈ X := hX
  unfold _root_.GlobalTheory.Mass.orbSum
  have hout : ∀ x : α, ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G α) x).out := fun x =>
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G α) x))))
  have hterm : ∀ x : α,
      ((ENat.card (MulAction.stabilizer G (Quotient.mk (MulAction.orbitRel G α) x).out) : ℕ∞) :
          ℝ≥0∞)⁻¹ * N (Quotient.mk (MulAction.orbitRel G α) x).out
        = ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
    intro x
    obtain ⟨g, hg⟩ := hout x
    rw [← hg, hN,
      ENat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv.symm]
  let e : {x // x ∈ s} → {q : MulAction.orbitRel.Quotient G α // q.out ∈ X} := fun x =>
    ⟨Quotient.mk _ x.1, by obtain ⟨g, hg⟩ := hout x.1; rw [← hg]; exact hX' g _ (hs _ x.2)⟩
  have he_inj : Function.Injective e := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hq : Quotient.mk (MulAction.orbitRel G α) x = Quotient.mk _ y := congrArg Subtype.val hxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))
    obtain ⟨z, -, hz⟩ := huniq x (hs x hx)
    have h1 := hz x ⟨hx, 1, one_smul G x⟩
    have h2 := hz y ⟨hy, g, hg⟩
    exact Subtype.ext (h1.trans h2.symm)
  have he_surj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨y, ⟨hy, g, hg⟩, -⟩ := huniq q.out hq
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    show Quotient.mk _ y = q
    calc Quotient.mk (MulAction.orbitRel G α) y = Quotient.mk _ q.out :=
          Quotient.sound (MulAction.orbitRel_apply.mpr
            (MulAction.mem_orbit_iff.mpr ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩))
      _ = q := Quotient.out_eq q
  rw [← (Equiv.ofBijective e ⟨he_inj, he_surj⟩).tsum_eq, tsum_fintype, ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun x _ => hterm x.1
end _root_.GlobalTheory.Mass
end GlobalTheory.Mass
