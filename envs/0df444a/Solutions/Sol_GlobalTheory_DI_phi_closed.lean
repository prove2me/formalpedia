-- Prove2me | solution 1 for GlobalTheory.DI.phi_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:12.412873+00:00
-- url     : https://prove2.me/submissions/8bb574f5-f750-4a99-8d96-cabf7438c2ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosed
import Theorems.Thm_GlobalTheory_DI_PhiClosed_Dtot_add
import Theorems.Thm_GlobalTheory_DI_PhiClosed_Dtot_smul_pow
import Theorems.Thm_GlobalTheory_DI_prodL_alt_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory.DI.PhiClosed
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  intro K _ V _ _ ι _ p _ _ d f h Φ hd hD hΦ
  have hA := (prodL_alt_closed p d f h hd hD).2
  have hz0 : Dtot d (0 : Finset ι → ExteriorAlgebra K V) = 0 := by
    funext t
    simp [Dtot, delta]
  have key : ∀ x : ExteriorAlgebra K V, ∀ c : K, Φ (c • x) ∅ = 0 ∧ Dtot d (Φ (c • x)) = 0 := by
    intro x
    have hx : x ∈ Submodule.span K
        (Set.range fun x : (n : ℕ) × (Fin n → V) => ExteriorAlgebra.ιMulti K x.1 x.2) := by
      rw [ExteriorAlgebra.ιMulti_span]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, v⟩, rfl⟩ := hy
      intro c
      rw [hΦ c a v]
      exact ⟨by rw [Pi.smul_apply, (hA a v).2, smul_zero],
        by rw [PhiClosed.Dtot_smul_pow p d hd, (hA a v).1, smul_zero]⟩
    | zero =>
      intro c
      simp [hz0]
    | add y z _ _ hy hz =>
      intro c
      rw [smul_add, map_add]
      exact ⟨by rw [Pi.add_apply, (hy c).1, (hz c).1, add_zero],
        by rw [PhiClosed.Dtot_add, (hy c).2, (hz c).2, add_zero]⟩
    | smul a y _ hy =>
      intro c
      rw [smul_smul]
      exact hy (c * a)
  exact ⟨fun x => by simpa using (key x 1).1, fun x => by simpa using (key x 1).2⟩
end GlobalTheory.DI
