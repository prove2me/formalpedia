-- Prove2me | solution 1 for GlobalTheory.HeisLine.ell_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:25:00.514074+00:00
-- url     : https://prove2.me/submissions/3e43602c-45d7-46ea-8399-20ef5c060c3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant


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
theorem _root_.solution
    (h1 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = (χ (t ⬝ᵥ y) : ℂ) * a.1 y) →
      (∀ η, b'.1 η = b.1 (η - t)) → B a' b = B a b')
    (g : SB (n → k)) (u : n → k) (hg' : (fun x => g.1 (x + u)) ∈ SB (n → k)) :
    ell χ μ B ⟨_, hg'⟩ = ell χ μ B g := by
  have hloc : {y : n → k | χ ((-u) ⬝ᵥ y) = 1} ∈ 𝓝 (0 : n → k) := by
    have h3 : IsLocallyConstant fun y : n → k => χ ((-u) ⬝ᵥ y) :=
      hχ.isLocallyConstant.comp_continuous (continuous_const.dotProduct continuous_id)
    filter_upwards [h3.eventually_eq 0] with y hy
    simpa using hy
  obtain ⟨s, hs⟩ := exists_box_subset
    (Filter.inter_mem (addChar_dotProduct_trivial_on_tsupport_nhds hχ g.2) (Filter.inter_mem (addChar_dotProduct_trivial_on_tsupport_nhds hχ hg') hloc))
  have a1 : admitted χ s g.1 := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).1
  have a2 : admitted χ s (fun x => g.1 (x + u)) := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).2.1
  rw [ell_eq hχ μ B h2 ⟨_, hg'⟩ a2, ell_eq hχ μ B h2 g a1]
  congr 1
  refine (h1 (ind s) (ind s) g ⟨_, hg'⟩ (-u) (fun y => ?_) (fun η => ?_)).symm
  · by_cases hy : y ∈ box n s
    · show (box n s).indicator (fun _ => (1 : ℂ)) y = _ * (box n s).indicator (fun _ => (1 : ℂ)) y
      rw [(hs hy).2.2]
      simp
    · show (box n s).indicator (fun _ => (1 : ℂ)) y = _ * (box n s).indicator (fun _ => (1 : ℂ)) y
      simp [Set.indicator_of_notMem hy]
  · show g.1 (η + u) = g.1 (η - -u)
    rw [sub_neg_eq_add]
end GlobalTheory.HeisLine
