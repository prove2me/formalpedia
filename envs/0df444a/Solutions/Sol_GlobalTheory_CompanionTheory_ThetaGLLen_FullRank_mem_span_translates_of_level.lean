-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.mem_span_translates_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:44.564076+00:00
-- url     : https://prove2.me/submissions/8f3f63f0-d7cd-4157-839e-9451ff3402da

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_orb_smul_mem_iff

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
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution : ∀ (H X : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace X] [MulAction H X] (ρ : Representation ℂ H (SB X)), (∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x)) → ∀ (K N : Subgroup H), IsCompact (K : Set H) → IsOpen (N : Set H) → N ≤ K → (∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N) → ∀ (x₀ : X) (v f : SB X), (∀ x, v.1 x = ((fun n : H => n • x₀) '' (N : Set H)).indicator (fun _ => (1 : ℂ)) x) → (∀ n ∈ N, ∀ x, f.1 (n • x) = f.1 x) → (∀ x, f.1 x ≠ 0 → x ∈ (fun κ : H => κ • x₀) '' (K : Set H)) → f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by
  intro H X _ _ _ _ _ ρ hρ K N hK hN hNK hnorm x₀ v f hv hinv hsupp
  classical
  obtain ⟨T, hTK, hT⟩ := hK.elim_nhds_subcover (fun κ : H => (fun n : H => κ * n) '' (N : Set H)) (fun κ _ =>
    ((Homeomorph.mulLeft κ).isOpenMap _ hN).mem_nhds ⟨1, N.one_mem, mul_one κ⟩)
  have hu : ∀ (τ : H) (x : X), (ρ τ v).1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) (τ⁻¹ • x) := fun τ x => by
    rw [hρ, hv]
  have key : ∀ (T : Finset H), (∀ τ ∈ T, τ ∈ K) → ∀ f : SB X, (∀ n ∈ N, ∀ x, f.1 (n • x) = f.1 x) →
      (∀ x, f.1 x ≠ 0 → ∃ τ ∈ T, τ⁻¹ • x ∈ orb N x₀) →
      f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ f _ hf
      have : f = 0 := Subtype.ext (funext fun x => by
        by_contra h
        obtain ⟨τ, hτ, -⟩ := hf x h
        simp at hτ)
      rw [this]
      exact Submodule.zero_mem _
    | insert τ T _ ih =>
      intro hTK f hfi hf
      have hτ : τ ∈ K := hTK τ (Finset.mem_insert_self _ _)
      have hst : ∀ n ∈ N, ∀ x, τ⁻¹ • n • x ∈ orb N x₀ ↔ τ⁻¹ • x ∈ orb N x₀ := fun n hn x => by
        have hm : τ⁻¹ * n * τ⁻¹⁻¹ ∈ N := hnorm _ (K.inv_mem hτ) n hn
        rw [inv_inv] at hm
        have e : τ⁻¹ • n • x = (τ⁻¹ * n * τ) • τ⁻¹ • x := by
          simp only [mul_smul, smul_inv_smul]
        rw [e, orb_smul_mem_iff hm]
      have hval : ∀ x, τ⁻¹ • x ∈ orb N x₀ → f.1 x = f.1 (τ • x₀) := by
        rintro x ⟨n, hn, e⟩
        have e' : n • x₀ = τ⁻¹ • x := e
        have hm : τ * n * τ⁻¹ ∈ N := hnorm τ hτ n hn
        have e2 : x = (τ * n * τ⁻¹) • τ • x₀ := by
          simp only [mul_smul, inv_smul_smul, e', smul_inv_smul]
        rw [e2, hfi _ hm]
      have hu1 : ∀ x, τ⁻¹ • x ∈ orb N x₀ → (ρ τ v).1 x = 1 := fun x hx => by
        rw [hu, Set.indicator_of_mem hx]
      have hu0 : ∀ x, τ⁻¹ • x ∉ orb N x₀ → (ρ τ v).1 x = 0 := fun x hx => by
        rw [hu, Set.indicator_of_notMem hx]
      have hv' : ∀ x, (f - f.1 (τ • x₀) • ρ τ v).1 x = f.1 x - f.1 (τ • x₀) * (ρ τ v).1 x := fun _ => rfl
      have hm := ih (fun σ hσ => hTK σ (Finset.mem_insert_of_mem hσ)) (f - f.1 (τ • x₀) • ρ τ v)
        (fun n hn x => by
          rw [hv', hv', hfi n hn x]
          by_cases hx : τ⁻¹ • x ∈ orb N x₀
          · rw [hu1 _ ((hst n hn x).2 hx), hu1 _ hx]
          · rw [hu0 _ (fun h => hx ((hst n hn x).1 h)), hu0 _ hx])
        (fun x hx => by
          rw [hv'] at hx
          by_cases hxτ : τ⁻¹ • x ∈ orb N x₀
          · rw [hu1 _ hxτ, hval x hxτ, mul_one, sub_self] at hx
            exact absurd rfl hx
          · rw [hu0 _ hxτ, mul_zero, sub_zero] at hx
            obtain ⟨σ, hσ, hm⟩ := hf x hx
            rcases Finset.mem_insert.1 hσ with rfl | hσ
            · exact absurd hm hxτ
            · exact ⟨σ, hσ, hm⟩)
      have e : f = (f - f.1 (τ • x₀) • ρ τ v) + f.1 (τ • x₀) • ρ τ v := by abel
      rw [e]
      exact Submodule.add_mem _ hm (Submodule.smul_mem _ _ (Submodule.subset_span ⟨τ, rfl⟩))
  refine key T hTK f hinv fun x hx => ?_
  obtain ⟨κ, hκ, rfl⟩ := hsupp x hx
  obtain ⟨τ, hτ, hm⟩ := Set.mem_iUnion₂.1 (hT hκ)
  obtain ⟨n, hn, rfl⟩ := hm
  refine ⟨τ, hτ, n, hn, ?_⟩
  show n • x₀ = τ⁻¹ • (τ * n) • x₀
  rw [mul_smul, inv_smul_smul]
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
