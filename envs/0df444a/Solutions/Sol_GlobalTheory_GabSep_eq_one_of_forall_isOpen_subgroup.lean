-- Prove2me | solution 1 for GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:35.511926+00:00
-- url     : https://prove2.me/submissions/d51e50e2-eb7d-40e6-8e2f-94d48a0c59f6

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.GabSep
namespace GlobalTheory.GabSep
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (g : Gab E Ω), (∀ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) → g ∈ U) → g = 1 := by
  intro E Ω _ _ _ _ g hg
  by_contra hne
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hT1 : T1Space (Gab E Ω) := inferInstance
  have hopen : IsOpen ({g}ᶜ : Set (Gab E Ω)) := isOpen_compl_singleton
  have hmem : ((QuotientGroup.mk : G E Ω → Gab E Ω) ⁻¹' {g}ᶜ) ∈ nhds (1 : G E Ω) := by
    refine (hopen.preimage QuotientGroup.continuous_mk).mem_nhds ?_
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, QuotientGroup.mk_one]
    exact fun h => hne h.symm
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hmem
  let V : Subgroup (Gab E Ω) := L.fixingSubgroup.map (QuotientGroup.mk' _)
  have hV : IsOpen (V : Set (Gab E Ω)) := by
    have : (V : Set (Gab E Ω)) = (QuotientGroup.mk : G E Ω → Gab E Ω) '' (L.fixingSubgroup : Set (G E Ω)) := by
      simp [V, Subgroup.coe_map]
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen L)
  obtain ⟨σ, hσ, e⟩ := Subgroup.mem_map.mp (hg V hV)
  exact hsub hσ (by simpa using e)
end GlobalTheory.GabSep
