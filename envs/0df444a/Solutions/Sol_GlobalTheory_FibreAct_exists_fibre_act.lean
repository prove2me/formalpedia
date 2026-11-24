-- Prove2me | solution 1 for GlobalTheory.FibreAct.exists_fibre_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:20.984874+00:00
-- url     : https://prove2.me/submissions/7a29214b-a152-46e9-bfa5-39b790549e27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreAct
import Theorems.Thm_GlobalTheory_FibreAct_isGrpPullback_of_iso
import Theorems.Thm_GlobalTheory_FibreAct_exists_lift_act
import Theorems.Thm_GlobalTheory_LiePull_lieMult_pull


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
open GlobalTheory GlobalTheory.FibreAct
namespace GlobalTheory.FibreAct
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H S) (x : Sp ℂ ⟶ S) (β : o →+* ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (m : A₀.left ⟶ t.A.left), IsPEL D a bas ρ t τ → x ≫ s = spMap β → IsGrpPullback A₀ t.A x m → ∃ (act : OAct (𝓞 E) t.A) (act₀ : OAct (𝓞 E) A₀), (∀ c, (act₀.act c).left ≫ m = m ≫ (act.act c).left) ∧ DetCond D act₀ (𝟙 _) (β ρ) := by
  intro E _ _ _ H D g k J a bas o _ b ρ S s t τ x β A₀ _ m hP hx hm
  obtain ⟨φ, hφ, -, -, hd⟩ := hP
  haveI := hφ
  have hi : IsGrpPullback t.A τ.G (𝟙 S) φ.inv.left := isGrpPullback_of_iso φ.inv
  obtain ⟨act, hact⟩ := exists_lift_act hi τ.act
  obtain ⟨act₀, hact₀⟩ := exists_lift_act hm act
  refine ⟨act, act₀, hact₀, fun σ => ?_⟩
  have L : ∀ n, LieMult act₀ (𝟙 _) σ n ↔ LieMult τ.act x σ n := fun n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hm hact₀ ℂ (𝟙 _) σ n,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.id_comp, Category.comp_id]
  rw [L, L]
  exact (hd ℂ x β hx).1 σ
end GlobalTheory.FibreAct
