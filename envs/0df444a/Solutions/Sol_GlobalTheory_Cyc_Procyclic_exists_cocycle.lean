-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.exists_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:52.097816+00:00
-- url     : https://prove2.me/submissions/d2b5194b-9545-4b47-9b72-869dffbbcf73

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_psum_add
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_psum_mem
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_exists_norm_psum_sub_le
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_eqOn_of_dense
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_exists_extension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Procyclic
variable {Γ X : Type} [Group Γ] [NormedAddCommGroup X]
variable {G : Subgroup Γ} {A : Γ → X →+ X} {g : Γ} {w : X}
variable [IsUltrametricDist X]
variable [TopologicalSpace Γ]
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution [CompleteSpace X] [ContinuousMul Γ] {H : Subgroup Γ} (p : ℕ)
    (Gn : ℕ → Subgroup Γ) (hanti : Antitone Gn) (M : AddSubgroup X) (hMc : IsClosed (M : Set X))
    (hg : g ∈ G) (hw : w ∈ M) (hHG : H ≤ G) (hHn : ∀ n, H ≤ Gn n)
    (hnorm : ∀ σ ∈ G, ∀ h ∈ H, σ * h * σ⁻¹ ∈ H) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y))
    (hn : ∀ σ ∈ G, ∀ y, ‖A σ y‖ ≤ ‖y‖) (hcont : ∀ y, ContinuousOn (fun σ => A σ y) G)
    (hAM : ∀ σ ∈ G, ∀ y ∈ M, A σ y ∈ M) (hHM : ∀ h ∈ H, ∀ y ∈ M, A h y = y)
    (hopen : ∀ N, ∀ σ ∈ G, ∀ᶠ τ in 𝓝[G] σ, τ * σ⁻¹ ∈ Gn N)
    (hcos : ∀ σ ∈ G, ∀ n, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gn n)
    (hd : (G : Set Γ) ⊆ closure {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a})
    (hdvd : ∀ k, ∃ N, ∀ d : ℕ, g ^ d ∈ Gn N → p ^ k ∣ d)
    (hD : ∀ ε > 0, ∃ k : ℕ, ‖A (g ^ p ^ k) w - w‖ ≤ ε)
    (hp : ∀ ε > 0, ∃ s : ℕ, ∀ y : X, ‖y‖ ≤ ‖w‖ → ‖p ^ s • y‖ ≤ ε) :
    ∃ c : Γ → X, ContinuousOn c G ∧ (∀ σ ∈ G, c σ ∈ M) ∧
      (∀ σ ∈ G, ∀ τ ∈ G, c (σ * τ) = c σ + A σ (c τ)) ∧ (∀ h ∈ H, c h = 0) ∧ c g = w := by
  have hS : ∀ ε > 0, ∃ N, ∀ a b : ℕ, g ^ a * (g ^ b)⁻¹ ∈ Gn N →
      ‖psum A g w a - psum A g w b‖ ≤ ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_norm_psum_sub_le p hg hone hmul hn hD hp ε hε
    obtain ⟨N, hN⟩ := hdvd k
    have h1 : ∀ a b : ℕ, b ≤ a → g ^ a * (g ^ b)⁻¹ ∈ Gn N →
        ‖psum A g w a - psum A g w b‖ ≤ ε := by
      intro a b hab h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      refine hk _ _ (hN d ?_)
      rwa [add_comm, pow_add, mul_inv_cancel_right] at h
    refine ⟨N, fun a b h => ?_⟩
    rcases le_total b a with hab | hab
    · exact h1 a b hab h
    · rw [norm_sub_rev]
      refine h1 b a hab ?_
      simpa using (Gn N).inv_mem h
  obtain ⟨c, hc⟩ := exists_extension Gn hanti hcos _ hS
  have hval : ∀ h ∈ H, ∀ a : ℕ, c (h * g ^ a) = psum A g w a := by
    intro h hh a
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hc ε hε
    rw [zero_add]
    refine hN _ (G.mul_mem (hHG hh) (pow_mem hg a)) a ?_
    rw [mul_inv_cancel_right]
    exact hHn N hh
  have hcc : ContinuousOn c G := by
    intro σ hσ
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
    obtain ⟨a, ha⟩ := hcos σ hσ N
    filter_upwards [hopen N σ hσ, self_mem_nhdsWithin] with τ hτ hτG
    have h1 : τ * (g ^ a)⁻¹ ∈ Gn N := by
      have := (Gn N).mul_mem hτ ha
      simpa [mul_assoc] using this
    have h2 : c τ - c σ = (c τ - psum A g w a) + -(c σ - psum A g w a) := by abel
    rw [dist_eq_norm, h2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact (hN τ hτG a h1).trans_lt (half_lt_self hε)
    · rw [norm_neg]; exact (hN σ hσ a ha).trans_lt (half_lt_self hε)
  have hSM : ∀ n, psum A g w n ∈ M := psum_mem hw (hAM g hg)
  have hcM : ∀ σ ∈ G, c σ ∈ M := by
    intro σ hσ
    change c σ ∈ (M : Set X)
    rw [← hMc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
    obtain ⟨a, ha⟩ := hcos σ hσ N
    exact ⟨_, hSM a, by rw [dist_eq_norm]; exact (hN σ hσ a ha).trans_lt (half_lt_self hε)⟩
  have hAc : ∀ σ ∈ G, Continuous (A σ) := fun σ hσ =>
    AddMonoidHomClass.continuous_of_bound (A σ) 1 (fun y => by rw [one_mul]; exact hn σ hσ y)
  refine ⟨c, hcc, hcM, ?_, fun h hh => ?_, ?_⟩
  · have hconj : ∀ h ∈ H, ∀ a : ℕ, ∀ τ ∈ G, c (h * g ^ a * τ) = c (h * g ^ a) + A (h * g ^ a) (c τ) := by
      intro h hh a
      have hσ : h * g ^ a ∈ G := G.mul_mem (hHG hh) (pow_mem hg a)
      refine eqOn_of_dense hg hHG hd (f₁ := fun τ => c (h * g ^ a * τ))
        (f₂ := fun τ => c (h * g ^ a) + A (h * g ^ a) (c τ)) ?_ ?_ fun h' hh' b => ?_
      · exact hcc.comp (continuous_const_mul _).continuousOn fun x hx => G.mul_mem hσ hx
      · exact continuousOn_const.add ((hAc _ hσ).comp_continuousOn hcc)
      · have h1 : h * g ^ a * (h' * g ^ b) = (h * (g ^ a * h' * (g ^ a)⁻¹)) * g ^ (a + b) := by
          rw [pow_add]; group
        rw [h1, hval _ (H.mul_mem hh (hnorm _ (pow_mem hg a) _ hh')), hval h hh, hval h' hh',
          hmul _ (hHG hh) _ (pow_mem hg a), hHM h hh _ (hAM _ (pow_mem hg a) _ (hSM b)),
          psum_add hg hone hmul]
    intro σ hσ τ hτ
    refine eqOn_of_dense hg hHG hd (f₁ := fun σ => c (σ * τ)) (f₂ := fun σ => c σ + A σ (c τ))
      ?_ (hcc.add (hcont _)) (fun h hh a => hconj h hh a τ hτ) σ hσ
    exact hcc.comp (continuous_mul_const τ).continuousOn fun x hx => G.mul_mem hx hτ
  · simpa [psum] using hval h hh 0
  · simpa [psum] using hval 1 H.one_mem 1
end GlobalTheory.Cyc.Procyclic
