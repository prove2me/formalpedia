-- Prove2me | solution 1 for GlobalTheory.VolFin.exists_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:12.921061+00:00
-- url     : https://prove2.me/submissions/d00f5394-13b0-4c67-a103-fd0687e5df55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
import Theorems.Thm_GlobalTheory_VolFin_gen_rs
import Theorems.Thm_GlobalTheory_VolFin_eq_of_gen
import Theorems.Thm_GlobalTheory_VolFin_exists_gen_eq
import Theorems.Thm_GlobalTheory_VolFin_tr_mul
import Theorems.Thm_GlobalTheory_VolFin_tr_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
open GlobalTheory GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
namespace GlobalTheory.VolFin
theorem _root_.solution {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (f : X.functionField)
    (hf : ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) :
    ∃ s : N.Sec, gen _ h₀ (s.f j₀) = f := by
  have H : ∀ j, ∃ a : Γ(X, N.U j), ∀ hj, gen _ hj a = tr N j j₀ hj h₀ * f := by
    intro j
    by_cases hj : genericPoint X ∈ N.U j
    · obtain ⟨a, ha⟩ := exists_gen_eq (N.U j) (tr N j j₀ hj h₀ * f) fun x hx => by
        obtain ⟨i, hi⟩ := hc x
        obtain ⟨a, ha⟩ := hf i
        refine ⟨N.U j ⊓ W i, ⟨hx, hi⟩,
          rs X (inf_le_inf_left _ (hW i)) (N.g j (c i)).val * rs X inf_le_right a, ?_⟩
        rw [map_mul, gen_rs, gen_rs, ha, ← tr_mul hN j (c i) j₀ hj (hW i (hη i)) h₀]
        unfold tr
        ring
      exact ⟨a, ha⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose a ha using H
  refine ⟨⟨a, fun i j => eq_of_gen fun h => ?_⟩, ?_⟩
  · rw [map_mul]
    refine (gen_rs _ _ _).trans ((ha i h.1).trans ?_)
    rw [← tr_mul hN i j j₀ h.1 h.2 h₀, _root_.mul_assoc, ← ha j h.2]
    exact congrArg _ (gen_rs (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) h (a j)).symm
  · rw [ha, tr_self hN, _root_.one_mul]
end GlobalTheory.VolFin
