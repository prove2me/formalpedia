-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:20:11.431125+00:00
-- url     : https://prove2.me/submissions/52370a6d-1a4b-4942-80d3-66e3004920ff

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_conv_comap
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_conv_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv
theorem _root_.solution : ParLaw → ConvU := by
  intro hPar E R _ _ _ _ _ _ _ A hA hGr ι _ _ ε s hIwa
  have inv : ∀ {H : Type} [Group H] [TopologicalSpace H] {Γ K P : Subgroup H} {η : H → ℝ} (c : ℝ),
      IsHt Γ K P η → ∀ γ ∈ Γ, γ ∈ P → ∀ g, c * η (γ * g) = c * η g := by
    intro H _ _ Γ K P η c h γ hγ hγP g
    rw [h.left γ hγP g, h.rat γ hγ hγP, zero_add]
  have hconv : ∀ (t : Set ι) (x : ℝ), (∀ g : A.U ε ι, A.uH ε t g = A.htGL (Sum.inl '' t) g.1) →
      IsHt (A.ratGL (ι ⊕ ι)) (A.kGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (A.htGL (Sum.inl '' t)) →
      Conv (A.ratGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (fun g => x * A.htGL (Sum.inl '' t) g) →
      Conv (A.uΓ ε ι) (A.uQ ε t) fun g => x * A.uH ε t g := by
    intro t x heq hHt hc
    have h := conv_comap (A.uSub ε ι).subtype (Γ := A.ratGL (ι ⊕ ι)) (P := stab R (Sum.inl '' t))
      (Γ' := A.uΓ ε ι) (P' := A.uQ ε t) (l := fun g => x * A.htGL (Sum.inl '' t) g)
      (fun γ hγ => Subgroup.mem_subgroupOf.mp hγ) (fun γ _ hγ => Subgroup.mem_subgroupOf.mpr hγ)
      (inv x hHt) hc
    have hfun : (fun g : A.U ε ι => x * A.uH ε t g) =
        fun g => x * A.htGL (Sum.inl '' t) ((A.uSub ε ι).subtype g) := by
      funext g
      exact congrArg (fun r => x * r) (heq g)
    rw [hfun]
    exact h
  have hIwaU : Iwa (A.uQ ε (Set.univ : Set ι) ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by
    intro g
    obtain ⟨p, hp, k, hk, hg⟩ := hIwa g
    exact ⟨p, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hp).2, (Subgroup.mem_inf.mp hp).2⟩, k, hk, hg⟩
  obtain ⟨Rs, hRs⟩ := hGr (ι ⊕ ι) (Sum.inl '' s)
  obtain ⟨Ru, hRu⟩ := hGr (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
  have hs := (hPar E R A hA ι ε s).2 hIwa
  have hu := (hPar E R A hA ι ε Set.univ).2 hIwaU
  have hGs := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' s)).1.2.2.2.1
  have hGu := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' (Set.univ : Set ι))).1.2.2.2.1
  refine ⟨max Rs Ru, fun y hy => ?_, fun x y hx hy => ?_⟩
  · exact hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy))
  · exact conv_inf (l₁ := fun g => x * A.uH ε s g) (l₂ := fun g => y * A.uH ε Set.univ g)
      (inv x hs.2.1) (inv y hu.2.1)
      (hconv s x hs.2.2 hGs (hRs x (lt_of_le_of_lt (le_max_left _ _) hx)))
      (hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy)))
end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
