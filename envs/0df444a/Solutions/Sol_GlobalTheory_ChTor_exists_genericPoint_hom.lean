-- Prove2me | solution 1 for GlobalTheory.ChTor.exists_genericPoint_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:03:25.448312+00:00
-- url     : https://prove2.me/submissions/581fdd8e-44a9-481f-894b-c60456422a98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ChartPoints_ChartPt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsGenericPointHom
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor
open GlobalTheory GlobalTheory.ChTor
namespace GlobalTheory.ChTor
theorem _root_.solution (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (G : Over (Sp O)) [GrpObj G] (hsep : IsSeparated G.hom)
    (A : Over (Sp C)) [GrpObj A] (gen : A.left ⟶ G.left)
    (h : IsGrpPullback A G (spMap (algebraMap O C)) gen) :
    ∃ j : (algOver O O ⟶ G) →* Pts A, Function.Injective j ∧
      ∀ P z, z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j P := by
  have hid : spMap (algebraMap O O) = 𝟙 (Sp O) := by
    simp [spMap]
  let e₀ : (Over.mk ((Over.mk (𝟙 (Sp C)) : Over (Sp C)).hom ≫ spMap (algebraMap O C)) : Over (Sp O)) ⟶ algOver O O :=
    Over.homMk (spMap (algebraMap O C)) (by
      change spMap (algebraMap O C) ≫ spMap (algebraMap O O) = 𝟙 _ ≫ spMap (algebraMap O C)
      rw [hid, Category.comp_id, Category.id_comp])
  have hw : ∀ P : algOver O O ⟶ G,
      (spMap (algebraMap O C) ≫ P.left) ≫ G.hom = 𝟙 (Sp C) ≫ spMap (algebraMap O C) := fun P => by
    have := Over.w (e₀ ≫ P)
    exact this
  let j₀ : (algOver O O ⟶ G) → Pts A := fun P =>
    Over.homMk (h.1.lift (spMap (algebraMap O C) ≫ P.left) (𝟙 (Sp C)) (hw P)) (h.1.lift_snd _ _ _)
  have hj : ∀ P, (j₀ P).left ≫ gen = spMap (algebraMap O C) ≫ P.left := fun P => h.1.lift_fst _ _ _
  have key : ∀ (P : algOver O O ⟶ G) (z : Pts A),
      z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j₀ P := fun P z => by
    constructor
    · intro hz
      refine Over.OverMorphism.ext (h.1.hom_ext (hz.trans (hj P).symm) ?_)
      exact (Over.w z).trans (Over.w (j₀ P)).symm
    · rintro rfl
      exact hj P
  have hmul : ∀ P Q, j₀ (P * Q) = j₀ P * j₀ Q := fun P Q => by
    refine ((key _ _).1 ?_).symm
    have e := h.2 _ (j₀ P) (j₀ Q) (e₀ ≫ P) (e₀ ≫ Q) (hj P).symm (hj Q).symm
    rw [← MonObj.comp_mul] at e
    exact e.symm
  refine ⟨MonoidHom.mk' j₀ hmul, fun P Q hPQ => ?_, key⟩
  have hPQ' : j₀ P = j₀ Q := hPQ
  haveI : IsDomain O := hinj.isDomain _
  haveI : IsDominant (spMap (algebraMap O C)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap O C)).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine Over.OverMorphism.ext ?_
  refine ext_of_isDominant_of_isSeparated (X := Sp O) G.hom ?_ (spMap (algebraMap O C)) ?_
  · exact (Over.w P).trans (Over.w Q).symm
  · exact (hj P).symm.trans (by rw [hPQ']; exact hj Q)
end GlobalTheory.ChTor
