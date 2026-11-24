-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:15.345077+00:00
-- url     : https://prove2.me/submissions/2ff7cc2d-c4ca-46fc-8ae7-a2e125ae332a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_ind_apply

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
theorem _root_.solution (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ (S : Finset G) (a : G → ℂ),
      f = ∑ t ∈ S, a t • pullHomeo (Homeomorph.mulRight t) (ind K hK) := by
  classical
  have hdisc : DiscreteTopology (G ⧸ (K : Subgroup G)) :=
    QuotientGroup.discreteTopology K.isOpen
  let π : G → G ⧸ (K : Subgroup G) := fun x => ((x⁻¹ : G) : G ⧸ (K : Subgroup G))
  have hπ : Continuous π := QuotientGroup.continuous_mk.comp continuous_inv
  have hfin : (π '' tsupport (f : G → ℂ)).Finite :=
    ((show IsCompact (tsupport (f : G → ℂ)) from f.2.2).image hπ).finite_of_discrete
  have key : ∀ (x : G) (q : G ⧸ (K : Subgroup G)), x * q.out ∈ K ↔ π x = q := by
    intro x q
    have h := QuotientGroup.eq (s := (K : Subgroup G)) (a := x⁻¹) (b := q.out)
    rw [inv_inv, QuotientGroup.out_eq'] at h
    exact h.symm
  have hinj : Set.InjOn (fun q : G ⧸ (K : Subgroup G) => q.out) (hfin.toFinset : Set _) :=
    fun a _ b _ h => Quotient.out_injective h
  refine ⟨hfin.toFinset.image (fun q => q.out), fun t => (f : G → ℂ) t⁻¹, ?_⟩
  rw [Finset.sum_image hinj]
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ hfin.toFinset,
      ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) : G → ℂ) x
        = if π x = q then (f : G → ℂ) x else 0 := by
    intro q _
    have e : ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) :
        G → ℂ) x = (f : G → ℂ) q.out⁻¹ * (ind K hK : G → ℂ) (x * q.out) := rfl
    rw [e, ind_apply]
    by_cases h : π x = q
    · have hm : x * q.out ∈ K := (key x q).2 h
      rw [if_pos h, Set.indicator_of_mem (show x * q.out ∈ (K : Set G) from hm), mul_one]
      have := hf _ hm q.out⁻¹
      rw [mul_inv_cancel_right] at this
      exact this.symm
    · rw [if_neg h, Set.indicator_of_notMem
        (show x * q.out ∉ (K : Set G) from fun hm => h ((key x q).1 hm)), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra h0
    exact h (hfin.mem_toFinset.2 ⟨x, subset_tsupport _ h0, rfl⟩)
end GlobalTheory.CompanionTheory.FrobHaarR
