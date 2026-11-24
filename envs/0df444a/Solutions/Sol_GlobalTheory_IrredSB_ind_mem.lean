-- Prove2me | solution 1 for GlobalTheory.IrredSB.ind_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:03.170512+00:00
-- url     : https://prove2.me/submissions/f14d81fd-9197-4e85-aca3-f54f0dcecd1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {G : Type} [AddCommGroup G]
namespace GlobalTheory.IrredSB
theorem _root_.solution {B : Type} (e : B → G → ℂ) (he : ∀ b t u, e b (t + u) = e b t * e b u)
    (W : Submodule ℂ (G → ℂ)) (hM : ∀ Φ ∈ W, ∀ b, (fun t => e b t * Φ t) ∈ W) (K : AddSubgroup G)
    (hsep : ∀ p ∉ K, ∃ b, (∀ u ∈ K, e b u = 1) ∧ e b p ≠ 1) {f : G → ℂ} (hf : f ∈ W)
    (h1 : ∀ u ∈ K, f u = 1) (P : Finset G) (hP : ∀ t, f t ≠ 0 → ∃ p ∈ P, ∃ u ∈ K, t = p + u) :
    ind K ∈ W := by
  classical
  have key : ∀ R : Finset G, ∃ Φ ∈ W, (∀ t ∈ K, Φ t = 1) ∧ (∀ t, f t = 0 → Φ t = 0) ∧
      ∀ r ∈ R, r ∉ K → ∀ u ∈ K, Φ (r + u) = 0 := by
    intro R
    induction R using Finset.induction_on with
    | empty => exact ⟨f, hf, h1, fun _ h => h, by simp⟩
    | insert r R _ ih =>
      obtain ⟨Φ, hΦ, k1, k2, k3⟩ := ih
      by_cases hr : r ∈ K
      · refine ⟨Φ, hΦ, k1, k2, fun s hs hsK u hu => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact absurd hr hsK
        · exact k3 s hs hsK u hu
      · obtain ⟨b, hb1, hne⟩ := hsep r hr
        have hne' : e b r - 1 ≠ 0 := sub_ne_zero.2 hne
        refine ⟨(e b r - 1)⁻¹ • (e b r • Φ - fun t => e b t * Φ t),
          Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ hΦ) (hM Φ hΦ b)), fun t ht => ?_,
          fun t ht => ?_, fun s hs hsK u hu => ?_⟩
        · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, k1 t ht, hb1 t ht, mul_one]
          exact inv_mul_cancel₀ hne'
        · simp [k2 t ht]
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · simp [he, hb1 u hu]
          · simp [k3 s hs hsK u hu]
  obtain ⟨Φ, hΦ, k1, k2, k3⟩ := key P
  convert hΦ using 1
  funext t
  by_cases ht : t ∈ K
  · simp [ind, ht, k1 t ht]
  · rw [ind, if_neg ht]
    by_cases hft : f t = 0
    · exact (k2 t hft).symm
    · obtain ⟨p, hp, u, hu, rfl⟩ := hP t hft
      exact (k3 p hp (fun hh => ht (add_mem hh hu)) u hu).symm
end GlobalTheory.IrredSB
