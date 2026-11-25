-- Prove2me | solution 1 for GlobalTheory.SatBlocks.saturated_blocks_summand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:42:03.874648+00:00
-- url     : https://prove2.me/submissions/4710bb96-f004-47c6-9170-0a7f6c9bd121

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand
import Theorems.Thm_GlobalTheory_SatBlocks_mem_intRing
import Theorems.Thm_GlobalTheory_SatBlocks_exists_projector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.SatBlocks
namespace GlobalTheory.SatBlocks
theorem _root_.solution : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (O A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → C), (∀ x i j, ((0 : ℝ) : WithTop ℝ) ≤ v (M x i j)) → (∀ a x, ((0 : ℝ) : WithTop ℝ) ≤ v (em a x)) → (∀ x q, (M x).mulVec (u q) = em q.1 x • u q) → (∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) → (∀ a, ∃ w : Fin d → Fin (n a) → C, (∀ s i, ((0 : ℝ) : WithTop ℝ) ≤ v (w s i)) ∧ ∀ i i', ∑ s, u ⟨a, i⟩ s * w s i' = if i = i' then 1 else 0) → ∃ w : Fin d → (Σ a : A, Fin (n a)) → C, (∀ s q, ((0 : ℝ) : WithTop ℝ) ≤ v (w s q)) ∧ ∀ q q', ∑ s, u q s * w s q' = if q = q' then 1 else 0 := by
  intro C _ v O A _ _ n d M em u hM he hu hs hw
  choose w hwi hw using hw
  have key := fun a : A => exists_projector v M em u hM he hu hs a (Finset.univ.erase a)
    (Finset.notMem_erase a _)
  choose P c hP hPu hca hcS using key
  refine ⟨fun s q => ∑ t, P q.1 t s * w q.1 t q.2, ?_, ?_⟩
  · intro s q
    exact (mem_intRing v _).1
      (sum_mem fun t _ => mul_mem (hP _ _ _) ((mem_intRing v _).2 (hwi _ _ _)))
  · rintro ⟨b, j⟩ ⟨a, i⟩
    have h1 : ∑ s, u ⟨b, j⟩ s * ∑ t, P a t s * w a t i
        = ∑ t, (P a).mulVec (u ⟨b, j⟩) t * w a t i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    dsimp only
    rw [h1, hPu]
    by_cases hba : b = a
    · subst hba
      simp only [hca, one_smul, hw]
      simp
    · have h0 : c a b = 0 := hcS a b (by simp [hba])
      rw [if_neg (fun h => hba (congrArg Sigma.fst h))]
      simp [h0]
end GlobalTheory.SatBlocks
