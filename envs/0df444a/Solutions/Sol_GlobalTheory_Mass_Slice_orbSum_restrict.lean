-- Prove2me | solution 1 for GlobalTheory.Mass.Slice.orbSum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:08.382844+00:00
-- url     : https://prove2.me/submissions/bfc61e3d-20b2-4b6d-aecc-3fc32dd1ec8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumRestrictSlice
import Theorems.Thm_GlobalTheory_Mass_Slice_exists_smul_eq_out
import Theorems.Thm_GlobalTheory_Mass_Slice_card_stabilizer_smul
import Theorems.Thm_GlobalTheory_Mass_Slice_card_stabilizer_subgroup

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Slice
namespace GlobalTheory.Mass.Slice
theorem _root_.solution : ∀ (G α : Type) [Group G] [MulAction G α] (H : Subgroup G) (X X₀ : Set α) (N : α → ℝ≥0∞), X₀ ⊆ X → Stable G X → Stable H X₀ → (∀ (g : G) x, N (g • x) = N x) → (∀ x ∈ X, ∃ g : G, g • x ∈ X₀) → (∀ (g : G), ∀ x ∈ X₀, g • x ∈ X₀ → g ∈ H) → orbSum H X₀ N = orbSum G X N := by
  intro G α _ _ H X X₀ N hsub hX hX₀ hN hmeet hret
  let f : {q : MulAction.orbitRel.Quotient H α // Quotient.out q ∈ X₀} →
      {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X} := fun q =>
    ⟨Quotient.mk (MulAction.orbitRel G α) (Quotient.out q.1), by
      obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
      rw [← hg]
      exact hX g _ (hsub q.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (MulAction.orbitRel G α) (Quotient.out a.1) (Quotient.out b.1) :=
      Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h1)
    have hgH : g ∈ H := hret g _ b.2 (hg ▸ a.2)
    have h2 : (MulAction.orbitRel H α) (Quotient.out a.1) (Quotient.out b.1) :=
      MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨g, hgH⟩, hg⟩)
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq b.1]
    exact Quotient.sound h2
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hmeet _ b.2
    obtain ⟨k, hk⟩ := exists_smul_eq_out H (g • Quotient.out b.1)
    refine ⟨⟨Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1), ?_⟩, ?_⟩
    · rw [← hk]; exact hX₀ k _ hg
    · apply Subtype.ext
      show Quotient.mk (MulAction.orbitRel G α)
        (Quotient.out (Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1))) = b.1
      rw [← hk]
      conv_rhs => rw [← Quotient.out_eq b.1]
      apply Quotient.sound
      refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨(k : G) * g, ?_⟩)
      rw [mul_smul]; rfl
  unfold orbSum
  rw [← (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
  have e : Quotient.out ((Equiv.ofBijective f ⟨hinj, hsurj⟩) q).1 = g • Quotient.out q.1 := hg.symm
  rw [e, hN, card_stabilizer_smul, card_stabilizer_subgroup H _
    (fun a ha => hret a _ q.2 (by rw [ha]; exact q.2))]
end GlobalTheory.Mass.Slice
