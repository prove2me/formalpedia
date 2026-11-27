-- Prove2me | solution 1 for GlobalTheory.ChF.embeddings_idempotents_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:42.575206+00:00
-- url     : https://prove2.me/submissions/16f87613-30c9-4340-8e3d-078c2d7fcffd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EmbeddingsLiftIntegersIdempotentsConjugation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
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


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem existsUnique_lift_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {OE : Type} [CommRing OE] [Module.Finite ℤ OE]
    (τ : OE →+* C) : ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ := by
  have h : ∀ x : OE, ∃ y : O, algebraMap O C y = τ x := fun x => by
    have h1 : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    have h2 : IsIntegral ℤ (τ x) := h1.map τ.toIntAlgHom
    have h3 : IsIntegral O (τ x) := h2.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h3)
  choose f hf using h
  refine ⟨{ toFun := f
            map_one' := hv.hom_inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hv.hom_inj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hv.hom_inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hv.hom_inj (by rw [hf, map_add, map_add, hf, hf]) }, ?_, ?_⟩
  · exact RingHom.ext hf
  · intro g hg
    refine RingHom.ext fun x => hv.hom_inj ?_
    change algebraMap O C (g x) = algebraMap O C (f x)
    rw [hf, ← hg]
    rfl
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  refine ⟨existsUnique_lift_integers hv, fun e τ he => ?_, ?_⟩
  · have h : IsIdempotentElem (tauExt τ e) := by
      unfold IsIdempotentElem
      rw [← map_mul, he]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h
  · intro _ τ x
    have h2 : sig p OE x = sigE p OE x := rfl
    refine ⟨?_, h2⟩
    rw [← h2]
    clear h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tauExt, sig]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
end GlobalTheory.ChF
