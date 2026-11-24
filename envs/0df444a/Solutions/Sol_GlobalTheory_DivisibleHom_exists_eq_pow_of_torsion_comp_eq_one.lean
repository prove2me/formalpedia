-- Prove2me | solution 1 for GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:07.989793+00:00
-- url     : https://prove2.me/submissions/1759b095-723b-4d5c-a7c3-b0559d0bc548

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
import Theorems.Thm_GlobalTheory_DivisibleHom_cancel_of_flat_surjective
import Theorems.Thm_GlobalTheory_DivisibleHom_mulA_comp
import Theorems.Thm_GlobalTheory_DivisibleHom_exists_factor
import Theorems.Thm_GlobalTheory_DivisibleHom_isMonHom_of_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.DivisibleHom
namespace _root_.GlobalTheory.DivisibleHom
theorem _root_.solution :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧ Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
        Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
          (IsUnit (n : Γ(S, ⊤)) → Etale (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left)) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (B : Over S) [GrpObj B]
      [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u →
        (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) →
          (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1) := by
  intro H S _ P B _ _ M hM u hu hkill
  obtain ⟨hfin, hflat, hsurj, -⟩ := H S P M hM
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  haveI := hu
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.DivisibleHom.exists_factor M u hkill
  haveI : IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M ≫ φ) := by rw [hφ]; infer_instance
  haveI := _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor M φ
  refine ⟨⟨φ, inferInstance, ?_⟩, fun h => ?_⟩
  · rw [← hφ, _root_.GlobalTheory.DivisibleHom.mulA_comp]
  · apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M)
    rw [_root_.GlobalTheory.DivisibleHom.mulA_comp, h, comp_one]
end _root_.GlobalTheory.DivisibleHom
end GlobalTheory.DivisibleHom
