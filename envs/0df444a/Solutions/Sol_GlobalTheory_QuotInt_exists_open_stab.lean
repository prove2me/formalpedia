-- Prove2me | solution 1 for GlobalTheory.QuotInt.exists_open_stab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:28.539813+00:00
-- url     : https://prove2.me/submissions/e10d7c4f-45e6-4ebb-91f1-69405e84de1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.QuotInt
theorem _root_.solution {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, F (g * x) = F g := by
  let K : Subgroup G :=
    { carrier := {x | ∀ g, F (g * x) = F g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        rw [← mul_assoc, hb, ha]
      inv_mem' := by
        intro a ha g
        have := ha (g * a⁻¹)
        simpa using this.symm }
  refine ⟨K, ?_, fun g x hx => hx g⟩
  have h1 : ∀ᶠ x in nhds (1 : G), ∀ g ∈ tsupport F, F (g * x) = F g := by
    apply IsCompact.eventually_forall_of_forall_eventually hF.2
    intro g _
    have a1 : IsLocallyConstant (fun z : G × G => F (z.2 * z.1)) :=
      hF.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun z : G × G => F z.2) :=
      hF.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (1, g), a2.eventually_eq (1, g)] with z hz1 hz2
    simp only [hz1, hz2, mul_one]
  have h2 : ∀ᶠ x in nhds (1 : G), ∀ g ∈ tsupport F, F (g * x⁻¹) = F g := by
    have : Filter.Tendsto (fun x : G => x⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact this.eventually h1
  apply Subgroup.isOpen_of_mem_nhds K (g := 1)
  filter_upwards [h1, h2] with x hx1 hx2
  intro g
  by_cases hg : g ∈ tsupport F
  · exact hx1 g hg
  · by_cases hg' : g * x ∈ tsupport F
    · simpa using (hx2 _ hg').symm
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']
end GlobalTheory.QuotInt
