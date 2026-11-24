-- Prove2me | solution 1 for GlobalTheory.splitTorus_hom_proper_trivial_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:10.387669+00:00
-- url     : https://prove2.me/submissions/e828a64c-e56b-4ea9-a09f-bc57eb24b951

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Theorems.Thm_GlobalTheory_TorusLocal_pullback_map_eq_one
import Theorems.Thm_GlobalTheory_TorusLocal_eq_one_of_isNilpotent_maximalIdeal
import Theorems.Thm_GlobalTheory_TorusLocal_eq_zero_of_forall_mem_map_pow
import Theorems.Thm_GlobalTheory_TorusLocal_pt_ext_of_quotients
import Theorems.Thm_GlobalTheory_TorusNil_comp_eq_of_pullback_map_eq
import Theorems.Thm_GlobalTheory_TorusNil_isIso_torusPt_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open TorusNil TorusLocal
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsProper B.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  have hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map (toUnit _ ≫ η[B]) := by
    intro n
    set J := IsLocalRing.maximalIdeal A ^ (n + 1) with hJ
    refine pullback_map_eq_one _ X B f hf fun g hg => ?_
    have hJt : J ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
    have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJt
    have : IsLocalRing (A ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk J)))).obj B).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    refine eq_one_of_isNilpotent_maximalIdeal (A ⧸ J) ⟨n + 1, ?_⟩ X _ g hg
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow, ← hJ, Ideal.map_quotient_self]
    rfl
  set t := torusPt A X (AddMonoidAlgebra.of A X) with ht
  have h1 : t ≫ f = t ≫ toUnit _ ≫ η[B] := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A (AddMonoidAlgebra A X)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap A (AddMonoidAlgebra A X ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1)).map
          (algebraMap A (AddMonoidAlgebra A X)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of A X
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]
end GlobalTheory
