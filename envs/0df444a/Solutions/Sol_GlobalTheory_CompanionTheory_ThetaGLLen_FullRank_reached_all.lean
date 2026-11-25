-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.reached_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:47.886189+00:00
-- url     : https://prove2.me/submissions/a9c0580c-0f57-46d4-9949-bcd66ed5076f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_clopen_cut
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_translate_mem_span
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_Reached_add
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_reached_of_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]
variable [T2Space X] [ContinuousSMul H X]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution [T2Space H] [TotallyDisconnectedSpace H] [MulAction.IsPretransitive H X]
    (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H))
    (hKo : IsOpen (K : Set H)) (x₀ : X) (f : SB X) : Reached ρ K x₀ f := by
  classical
  have hYc : IsCompact (orb K x₀) := hK.image (continuous_id.smul continuous_const)
  have hY : IsClopen (orb K x₀) := ⟨hYc.isClosed, hopen x₀ _ hKo⟩
  have hZ : ∀ g : H, IsClopen {x : X | g⁻¹ • x ∈ orb K x₀} := fun g =>
    hY.preimage (continuous_const_smul g⁻¹)
  have key : ∀ (T : Finset H) (f : SB X), (∀ x, f.1 x ≠ 0 → ∃ g ∈ T, g⁻¹ • x ∈ orb K x₀) →
      Reached ρ K x₀ f := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro f hf
      refine reached_of_support ρ hρ hopen hK hKo x₀ f fun x hx => ?_
      obtain ⟨g, hg, -⟩ := hf x hx
      simp at hg
    | insert g T hg ih =>
      intro f hf
      obtain ⟨f₁, f₂, e, h₁, h₂⟩ := exists_clopen_cut X _ (hZ g) f
      have r₁ : Reached ρ K x₀ f₁ := by
        obtain ⟨N, hN, v, hv, hm⟩ := reached_of_support ρ hρ hopen hK hKo x₀ (ρ g⁻¹ f₁) (fun x hx => by
          rw [hρ, inv_inv] at hx
          simpa using (h₁ _ hx).1)
        refine ⟨N, hN, v, hv, ?_⟩
        have := translate_mem_span ρ v g hm
        rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
      have r₂ : Reached ρ K x₀ f₂ := ih f₂ fun x hx => by
        obtain ⟨hx₁, hx₂⟩ := h₂ x hx
        obtain ⟨g', hg', hm⟩ := hf x hx₂
        rcases Finset.mem_insert.1 hg' with rfl | hg'
        · exact absurd hm hx₁
        · exact ⟨g', hg', hm⟩
      obtain ⟨N, hN, v, hv, m₁, m₂⟩ := r₁.add hρ hopen hK r₂
      exact ⟨N, hN, v, hv, e ▸ Submodule.add_mem _ m₁ m₂⟩
  obtain ⟨T, hT⟩ := f.2.2.elim_finite_subcover (fun g : H => {x : X | g⁻¹ • x ∈ orb K x₀})
    (fun g => (hZ g).isOpen) (fun x _ => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H x₀ x
      exact Set.mem_iUnion.2 ⟨g, 1, K.one_mem, by
        show (1 : H) • x₀ = g⁻¹ • x
        rw [one_smul, ← hg, inv_smul_smul]⟩)
  exact key T f fun x hx => by
    simpa using hT (subset_tsupport _ hx)
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
