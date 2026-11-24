-- Prove2me | solution 1 for GlobalTheory.sec_relation_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:29.296313+00:00
-- url     : https://prove2.me/submissions/033ba0b3-8a6c-496c-bfe8-da1163db29c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZeroStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Theorems.Thm_GlobalTheory_T_sec_eq_zero_of_sval_whiskerRight_zero
import Theorems.Thm_GlobalTheory_exists_sec_relation_defect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (z : (T' ⊗ B).left) (J), Good L z J → gs (ψ ▷ B).left z ⊤ c' * sval s' (ψ ▷ B).left z J = gs (ψ ▷ B).left z ⊤ c * (sval s ((ψ ▷ B).left ≫ τ) z J * (val u (ψ ▷ B).left z J).val)) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro S B T T' _ _ _ ψ hψ X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := GlobalTheory.T.sec_eq_zero_of_sval_whiskerRight_zero S B T T' ψ hψ X L hL K' φ' ε' d
    (fun z J hJ => (hd _ _ z J hJ).trans (sub_eq_zero.2 (h z J hJ)))
  refine sub_eq_zero.1 ((hd Z r z J hJ).symm.trans ?_)
  refine (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)
end GlobalTheory
