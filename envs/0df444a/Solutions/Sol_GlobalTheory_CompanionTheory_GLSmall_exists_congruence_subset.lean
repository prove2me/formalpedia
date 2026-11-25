-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLSmall.exists_congruence_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:48.486413+00:00
-- url     : https://prove2.me/submissions/ea76fd5d-7feb-4ca7-9a6a-c17fe1ebeb2e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence
import Theorems.Thm_GlobalTheory_CompanionTheory_GLSmall_small_antitone
import Theorems.Thm_GlobalTheory_CompanionTheory_GLSmall_tendsto_one_of_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLSmall
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.GLSmall
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), IsOpen U →
    (1 : GL (Fin n) k) ∈ U → ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ g : GL (Fin n) k,
    (∀ i j, ∃ μ ∈ 𝒪[k], (g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j = ϖ ^ l * μ) →
    (∀ i j, ∃ μ ∈ 𝒪[k], ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j = ϖ ^ l * μ) →
    g ∈ U := by
  intro k _ _ _ _ n U hU h1 ϖ hϖ
  have ha : Tendsto (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
      (⨅ l, 𝓟 (small ϖ n l)) (𝓝 1) :=
    tendsto_one_of_le_pow hϖ _ fun l _ ha => ha.1
  have hb : Tendsto (fun g : GL (Fin n) k => ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
      (⨅ l, 𝓟 (small ϖ n l)) (𝓝 1) :=
    tendsto_one_of_le_pow hϖ _ fun l _ ha => ha.2
  have ht : Tendsto (id : GL (Fin n) k → GL (Fin n) k) (⨅ l, 𝓟 (small ϖ n l)) (𝓝 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have hc := ha.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hb)
    rw [map_one]
    exact hc
  have hU' : U ∈ ⨅ l, 𝓟 (small ϖ n l) := ht (hU.mem_nhds h1)
  have hd : Directed (· ≥ ·) fun l => 𝓟 (small ϖ n l) :=
    (monotone_principal.comp_antitone (small_antitone hϖ n)).directed_ge
  obtain ⟨l, hl⟩ := (mem_iInf_of_directed hd U).1 hU'
  refine ⟨l, fun g hg hg' => mem_principal.1 hl ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · obtain ⟨μ, hμ, e⟩ := hg i j
    rw [e, map_mul, map_pow]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 hμ)
  · obtain ⟨μ, hμ, e⟩ := hg' i j
    rw [e, map_mul, map_pow]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 hμ)
end GlobalTheory.CompanionTheory.GLSmall
