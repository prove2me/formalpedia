-- Prove2me | solution 1 for GlobalTheory.grpObj_of_flat_coset_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:27.132455+00:00
-- url     : https://prove2.me/submissions/ed8df893-1c1f-4263-95d5-149ca9107d8b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
import Theorems.Thm_GlobalTheory_CosetQuotient_exists_grpObj
import Theorems.Thm_GlobalTheory_CosetQuotient_effectiveEpi_of_left
import Theorems.Thm_GlobalTheory_CosetQuotient_flat_tensorHom
import Theorems.Thm_GlobalTheory_CosetQuotient_surjective_tensorHom
import Theorems.Thm_GlobalTheory_CosetQuotient_quasiCompact_tensorHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (G T B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj T] (i : T ⟶ G)
      (q : G ⟶ B), IsMonHom i → Mono i → Flat q.left → Surjective q.left →
      QuasiCompact q.left →
      (∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) →
      ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  intro S G T B _ _ _ i q hi hm hf hs hc h
  have e1 : EffectiveEpi q := CosetQuotient.effectiveEpi_of_left q
  have f2 := CosetQuotient.flat_tensorHom q q
  have s2 := CosetQuotient.surjective_tensorHom q q
  have c2 := CosetQuotient.quasiCompact_tensorHom q q
  have e2 : EffectiveEpi (q ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  have f3 := CosetQuotient.flat_tensorHom (q ⊗ₘ q) q
  have s3 := CosetQuotient.surjective_tensorHom (q ⊗ₘ q) q
  have c3 := CosetQuotient.quasiCompact_tensorHom (q ⊗ₘ q) q
  have e3 : EffectiveEpi ((q ⊗ₘ q) ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  exact CosetQuotient.exists_grpObj i q h
end GlobalTheory
