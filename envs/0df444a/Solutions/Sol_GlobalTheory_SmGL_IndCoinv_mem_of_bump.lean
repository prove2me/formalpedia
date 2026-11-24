-- Prove2me | solution 1 for GlobalTheory.SmGL.IndCoinv.mem_of_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:59.126796+00:00
-- url     : https://prove2.me/submissions/8f1e0569-8ea5-4d6e-a596-102681d7c1c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
import Theorems.Thm_GlobalTheory_SmGL_IndDual_mem_span_bump
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_smoothRep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndCoinv
variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}
namespace GlobalTheory.SmGL.IndCoinv
theorem _root_.solution {K : Subgroup G} (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hb : ∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (Z : Submodule ℂ (smoothPart (ind P σ))) (hZ : ∀ g, ∀ f ∈ Z, smInd P σ g f ∈ Z)
    (h : ∀ (J : Subgroup G) (hJ : IsOpen (J : Set G)), J ≤ K → ∀ w, bump σ hJ w ∈ Z)
    (f : smoothPart (ind P σ)) : f ∈ Z := by
  obtain ⟨J, hJ, hJU, hle, hn⟩ := hb _ (IsOpen.mem_nhds (isSmooth_smoothRep _ f) (by
    rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply]))
  refine Submodule.span_le.2 ?_ (mem_span_bump σ hJ hK hle hn hPK f fun j hj => hJU hj)
  rintro _ ⟨z, -, w, rfl⟩
  exact hZ _ _ (h J hJ hle w)
end GlobalTheory.SmGL.IndCoinv
