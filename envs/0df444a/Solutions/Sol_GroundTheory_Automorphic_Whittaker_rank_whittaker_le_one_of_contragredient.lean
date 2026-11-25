-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rank_whittaker_le_one_of_contragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:21.179065+00:00
-- url     : https://prove2.me/submissions/ad8562c9-6d0b-409d-b1c7-700879e108fb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_biEquivariantSigmaInvariant_GL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_map_sigma_eq
import Theorems.Thm_GroundTheory_Automorphic_Measures_inv_eq_self_GL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rank_le_one_of_ne_bot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open MeasureTheory Measure ValuativeRel
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀)
    (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible]
    (hne : equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_le_one_of_ne_bot (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ hne
end GroundTheory.Automorphic.Whittaker
