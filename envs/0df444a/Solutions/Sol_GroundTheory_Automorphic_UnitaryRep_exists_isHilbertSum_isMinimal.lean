-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.exists_isHilbertSum_isMinimal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:54.513383+00:00
-- url     : https://prove2.me/submissions/0938db8f-7d8d-4f69-88e0-5485b85ed5ff

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_isMinimal_le
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_iSup
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_orthogonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f))) :
    ∃ s : Set (Submodule ℂ H), ∃ _ : ∀ V : s, CompleteSpace (V : Submodule ℂ H),
      (∀ V ∈ s, π.IsMinimal V) ∧
      IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ H)) fun V => (V : Submodule ℂ H).subtypeₗᵢ := by
  classical
  let S : Set (Set (Submodule ℂ H)) :=
    {s | (∀ V ∈ s, π.IsMinimal V) ∧ s.Pairwise fun V V' => V ⟂ V'}
  obtain ⟨s, hs⟩ := zorn_subset S fun c hcS hc => by
    refine ⟨⋃₀ c, ⟨fun V hV => ?_, fun V hV V' hV' hne => ?_⟩, fun t ht => Set.subset_sUnion_of_mem ht⟩
    · obtain ⟨t, ht, hVt⟩ := Set.mem_sUnion.1 hV
      exact (hcS ht).1 V hVt
    · obtain ⟨t, ht, hVt⟩ := Set.mem_sUnion.1 hV
      obtain ⟨t', ht', hVt'⟩ := Set.mem_sUnion.1 hV'
      rcases hc.total ht ht' with h | h
      · exact (hcS ht').2 (h hVt) hVt' hne
      · exact (hcS ht).2 hVt (h hVt') hne
  obtain ⟨hsmin, hsort⟩ := hs.1
  have hcomp : ∀ V : s, CompleteSpace (V : Submodule ℂ H) := fun V =>
    (hsmin V V.2).1.completeSpace_coe
  refine ⟨s, hcomp, hsmin, ?_⟩
  set M : Submodule ℂ H := ⨆ V : s, (V : Submodule ℂ H) with hM
  have hMinv : π.IsInvariant Mᗮ := (IsInvariant.iSup fun V : s => (hsmin V V.2).2.1).orthogonal
  have hMbot : Mᗮ = ⊥ := by
    by_contra hne
    obtain ⟨U, hU, hUM⟩ :=
      exists_isMinimal_le hcpt (Submodule.isClosed_orthogonal M) hMinv hne
    have hUV : ∀ V ∈ s, U ⟂ V := fun V hV => by
      rw [Submodule.isOrtho_iff_le]
      refine hUM.trans (Submodule.orthogonal_le ?_)
      exact le_iSup (fun V : s => (V : Submodule ℂ H)) ⟨V, hV⟩
    have hUs : U ∉ s := fun hUs => by
      have h1 : U ≤ M := le_iSup (fun V : s => (V : Submodule ℂ H)) ⟨U, hUs⟩
      apply hU.2.2.1
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ M ⊓ Mᗮ := ⟨h1 hx, hUM hx⟩
      rwa [Submodule.inf_orthogonal_eq_bot] at this
    have hins : insert U s ∈ S := by
      refine ⟨fun V hV => ?_, ?_⟩
      · rcases Set.mem_insert_iff.1 hV with rfl | hV
        · exact hU
        · exact hsmin V hV
      · rw [Set.pairwise_insert]
        exact ⟨hsort, fun V hV _ => ⟨hUV V hV, (hUV V hV).symm⟩⟩
    exact hUs (hs.2 hins (Set.subset_insert U s) (Set.mem_insert U s))
  refine IsHilbertSum.mkInternal _ (orthogonalFamily_iff_pairwise.mpr fun V V' hne =>
    hsort V.2 V'.2 fun h => hne (Subtype.ext h)) ?_
  rw [← hM, Submodule.topologicalClosure_eq_top_iff.2 hMbot]
end GroundTheory.Automorphic.UnitaryRep
