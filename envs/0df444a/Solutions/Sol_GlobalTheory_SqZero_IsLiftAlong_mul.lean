-- Prove2me | solution 1 for GlobalTheory.SqZero.IsLiftAlong.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:00:13.662106+00:00
-- url     : https://prove2.me/submissions/d10a7a22-7b2e-456b-96a4-9c83752603e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_comp_eq_one_of_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
omit [IsCommMonObj G] [Smooth G.hom]
namespace GlobalTheory.SqZero
namespace IsLiftAlong
theorem _root_.solution {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G} {φ : A →ₐ[R] T} {y z : sp T ⟶ G}
    (h : IsLiftAlong y₀ φ y) (hz : z ∈ redKer G (J.map φ)) : IsLiftAlong y₀ φ (z * y) := by
  intro T₀ _ _ q q₀ hq
  have hz' : spMap q ≫ z = 1 := comp_eq_one_of_mem_redKer hz q (fun a ha => RingHom.mem_ker.1 (Ideal.map_le_iff_le_comap.2 (fun b hb => Ideal.mem_comap.2 (RingHom.mem_ker.2 (by
        have := AlgHom.congr_fun hq b
        simpa [Ideal.Quotient.eq_zero_iff_mem.2 hb] using this))) ha))
  rw [← ptsMap_apply, map_mul, ptsMap_apply, ptsMap_apply, hz', one_mul]
  exact h T₀ q q₀ hq
end IsLiftAlong
end GlobalTheory.SqZero
