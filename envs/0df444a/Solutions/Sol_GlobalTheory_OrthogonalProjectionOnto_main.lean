-- Prove2me | solution 1 for GlobalTheory.OrthogonalProjectionOnto.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:56:10.024793+00:00
-- url     : https://prove2.me/submissions/f51d3cfd-acfa-4a19-9620-4b89c9a1d0bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EndoApplyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.OrthogonalProjectionOnto
open Module
namespace GlobalTheory.OrthogonalProjectionOnto
theorem _root_.solution : ∀ {R : Type u_1} [inst : Ring R] {ι : Type u_2} [Fintype ι] [inst_2 : DecidableEq ι]
    (M : ι → Type u_3) [inst_3 : (i : ι) → AddCommGroup (M i)] [inst_4 : (i : ι) → Module R (M i)]
    [∀ (i : ι), IsSimpleModule R (M i)],
    (∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = (0 : M i →ₗ[R] M j)) →
    ∀ (i₀ : ι) (s : (i : ι) → Finset (M i)), ∃ (r : R), ∀ (i : ι), ∀ m ∈ s i,
      r • m = if i = i₀ then m else (0 : M i) := by
  intro R _ ι _ _ M _ _ _ h i₀ s
  letI : DecidableEq (Π i, M i) := Classical.decEq _
  obtain ⟨r, hr⟩ := jacobson_density (R := R) (M := Π i, M i) (projOnto M h i₀)
    (Finset.univ.biUnion fun i => (s i).image (Pi.single i))
  refine ⟨r, fun i m hm => ?_⟩
  have hmem : Pi.single i m ∈ Finset.univ.biUnion fun i => (s i).image (Pi.single (M := M) i) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨i, m, hm, rfl⟩
  have := congrFun (hr _ hmem) i
  simp only [projOnto, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, Pi.smul_apply] at this
  exact this.symm
end GlobalTheory.OrthogonalProjectionOnto
