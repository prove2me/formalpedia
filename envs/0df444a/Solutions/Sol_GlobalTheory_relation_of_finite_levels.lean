-- Prove2me | solution 1 for GlobalTheory.relation_of_finite_levels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:44.686743+00:00
-- url     : https://prove2.me/submissions/b5256de8-c044-42e2-8110-70a1f7a763d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RelationOfFiniteLevels
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mem
import Theorems.Thm_GlobalTheory_exists_sec_relation_defect
import Theorems.Thm_GlobalTheory_sec_eq_zero_of_sval_finite_level


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro R _ I T B _ _ _ _ _ hI X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := sec_eq_zero_of_sval_finite_level R I T B hI X L hL K' φ' ε' d (fun e Z r hr z J hJ => by
    rw [hd Z r z J hJ, h e Z r hr z J hJ, sub_self])
  rw [← sub_eq_zero, ← hd Z r z J hJ]
  exact (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))
end GlobalTheory
