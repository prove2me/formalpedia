-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.exists_open_left_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:16.994611+00:00
-- url     : https://prove2.me/submissions/34e4ee16-1c9e-4ae2-a394-59ea29b66326

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.FrobHaarR
theorem _root_.solution {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ x, F (k * x) = F x := by
  let K : Subgroup G :=
    { carrier := {k | ∀ g, F (k * g) = F g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        rw [mul_assoc, ha, hb]
      inv_mem' := by
        intro a ha g
        have := ha (a⁻¹ * g)
        simpa using this.symm }
  have h1 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k * g) = F g := by
    apply IsCompact.eventually_forall_of_forall_eventually hF.2
    intro g _
    have a1 : IsLocallyConstant (fun z : G × G => F (z.1 * z.2)) :=
      hF.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun z : G × G => F z.2) :=
      hF.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (1, g), a2.eventually_eq (1, g)] with z hz1 hz2
    simp only [hz1, hz2, one_mul]
  have h2 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k⁻¹ * g) = F g := by
    have : Filter.Tendsto (fun x : G => x⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact this.eventually h1
  have hK : IsOpen (K : Set G) := by
    apply Subgroup.isOpen_of_mem_nhds K (g := 1)
    filter_upwards [h1, h2] with k hk1 hk2
    intro g
    by_cases hg : g ∈ tsupport F
    · exact hk1 g hg
    · by_cases hg' : k * g ∈ tsupport F
      · simpa using (hk2 _ hg').symm
      · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']
  exact ⟨⟨K, hK⟩, fun k hk x => hk x⟩
end GlobalTheory.CompanionTheory.FrobHaarR
