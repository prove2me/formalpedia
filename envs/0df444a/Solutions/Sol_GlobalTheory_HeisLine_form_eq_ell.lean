-- Prove2me | solution 1 for GlobalTheory.HeisLine.form_eq_ell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:25:02.05419+00:00
-- url     : https://prove2.me/submissions/0e58fe67-599f-44b5-b0bc-0997453e982f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.HeisLine
open GlobalTheory.SplitWeil.FourierPi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]
variable [MeasurableSpace k] [BorelSpace k]
variable {χ : AddChar k Circle} {c : kˣ}
variable (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
include hχ h2
namespace GlobalTheory.HeisLine
theorem _root_.solution (a b : SB (n → k))
    (hm : (fun η => (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η) ∈ SB (n → k)) :
    B a b = ell χ μ B ⟨_, hm⟩ := by
  haveI := secondCountable k
  obtain ⟨s, hs⟩ := exists_box_subset (Filter.inter_mem (invariant_nhds a.2) (addChar_dotProduct_trivial_on_tsupport_nhds hχ hm))
  have a1 : admitted χ s (fun η => (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η) :=
    isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).2
  rw [ell_eq hχ μ B h2 ⟨_, hm⟩ a1]
  have key := law_integrated hχ μ B h2 (ind s) b a ((μ.real (box n s) : ℂ) • a) ⟨_, hm⟩
    (fun y => by
      show (μ.real (box n s) : ℂ) * a.1 y = ∫ t, a.1 t * (box n s).indicator (fun _ => (1 : ℂ)) (y - t) ∂μ
      rw [conv_ind μ s a.2 (fun t ht x => (hs ht).1 x) y]) (fun η => rfl)
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
  rw [← key]
  field_simp [measureReal_box_ne μ s]
end GlobalTheory.HeisLine
