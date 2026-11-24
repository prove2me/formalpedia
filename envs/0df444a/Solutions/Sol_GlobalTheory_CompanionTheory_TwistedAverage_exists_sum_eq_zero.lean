-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.exists_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:03:59.750287+00:00
-- url     : https://prove2.me/submissions/21ac6395-4822-4615-bc95-dfc1417c0b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_sum_out_mul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_twOrbit_mul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_twOrbit_gen
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_twOrbit_add
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_twOrbit_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_finiteIndex_stabKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.TwistedAverage
theorem _root_.solution {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {v : V}
    (hv : v ∈ twKer ρ L θ) :
    ∃ M : Subgroup L, M.FiniteIndex ∧ ∀ (N : Subgroup L) [N.Normal] [Fintype (L ⧸ N)], N ≤ M →
      ∑ q : L ⧸ N, twOrbit ρ L θ v q.out = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, w, rfl⟩ := hx
    refine ⟨stabKer ρ L θ w, finiteIndex_stabKer hρ hL θ hθ w, ?_⟩
    intro N _ _ hN
    have hf : ∀ x, ∀ k ∈ N, twOrbit ρ L θ w (x * k) = twOrbit ρ L θ w x :=
      fun x k hk => twOrbit_mul_right ρ L θ w x k (hN hk)
    simp only [twOrbit_gen]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib,
      sum_out_mul_right N (twOrbit ρ L θ w) hf l, sub_self, smul_zero]
  | zero =>
    refine ⟨⊤, inferInstance, ?_⟩
    intro N _ _ _
    simp [twOrbit]
  | add x y _ _ hx hy =>
    obtain ⟨M₁, h₁, s₁⟩ := hx
    obtain ⟨M₂, h₂, s₂⟩ := hy
    refine ⟨M₁ ⊓ M₂, inferInstance, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_add]
    rw [Finset.sum_add_distrib, s₁ N (hN.trans inf_le_left), s₂ N (hN.trans inf_le_right), add_zero]
  | smul c x _ hx =>
    obtain ⟨M, h, s⟩ := hx
    refine ⟨M, h, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_smul]
    rw [← Finset.smul_sum, s N hN, smul_zero]
end GlobalTheory.CompanionTheory.TwistedAverage
