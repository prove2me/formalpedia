-- Prove2me | solution 1 for GlobalTheory.SegreCoord.box_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:28.707074+00:00
-- url     : https://prove2.me/submissions/a41cae1f-8de1-4906-8952-ab6c8dededea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_Loc_baseChange
import Theorems.Thm_GlobalTheory_SegreCoord_exists_away
import Theorems.Thm_GlobalTheory_SegreCoord_eq_top_of_away
import Theorems.Thm_GlobalTheory_SegreCoord_eq_of_away
import Theorems.Thm_GlobalTheory_SegreCoord_span_map
import Theorems.Thm_GlobalTheory_SegreCoord_unimod_smul
import Theorems.Thm_GlobalTheory_SegreCoord_unimod_mul
import Theorems.Thm_GlobalTheory_SegreCoord_rep_smul
import Theorems.Thm_GlobalTheory_SegreCoord_box_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {R : Type} [CommRing R] (I : Ideal (MvPolynomial σ R))
variable {I} {s : X ⟶ Sp R} (H : ProjRep I s M th) {Y : Scheme.{0}} {p q : Y ⟶ X} (hP : IsPullback p q s s)
include H hP
namespace GlobalTheory.SegreCoord
theorem _root_.solution {β : R →+* T} {x : Sp T ⟶ Y} (hx : x ≫ p ≫ s = spMap β) {w : σ × σ → T}
    (hw : Loc (boxLB M p q) (boxTh th p q) x w) : Ideal.span (Set.range w) = ⊤ ∧ RankOne I β w := by
  have key : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal,
      Ideal.span (Set.range fun i => algebraMap T (Localization.Away f) (w i)) = ⊤ ∧
      RankOne I ((algebraMap T (Localization.Away f)).comp β) (fun i => algebraMap T (Localization.Away f) (w i)) := by
    intro y
    obtain ⟨j, hj⟩ := exists_chart H.1 ((x ≫ p) y)
    obtain ⟨k, hk⟩ := exists_chart H.1 ((x ≫ q) y)
    obtain ⟨f, hf, hW⟩ := exists_away ((x ≫ p) ⁻¹ᵁ M.U j ⊓ (x ≫ q) ⁻¹ᵁ M.U k) y ⟨hj, hk⟩
    obtain ⟨v₁, v₂, t, ht, e, h₁, h₂⟩ := box_local H hP (β := (algebraMap T (Localization.Away f)).comp β)
      (by rw [Category.assoc, hx, ← spMap_comp]) (hw.baseChange (algebraMap T (Localization.Away f)))
      (fun z => (hW z).1) (fun z => (hW z).2)
    refine ⟨f, hf, ?_, fun a b c d => ?_, fun b F hF => ?_, fun a F hF => ?_⟩
    · rw [funext e]; exact unimod_smul (unimod_mul h₁.2.1 h₂.2.1) ht
    · simp only [e]; ring
    · rw [← rep_smul H h₁.2.1 h₁.2.2 (t * v₂ b) F hF]
      congr 1; funext i; simp only [e]; ring
    · rw [← rep_smul H h₂.2.1 h₂.2.2 (t * v₁ a) F hF]
      congr 1; funext i; simp only [e]; ring
  refine ⟨eq_top_of_away fun y => ?_, fun a b c d => eq_of_away fun y => ?_, fun b F hF => eq_of_away fun y => ?_,
    fun a F hF => eq_of_away fun y => ?_⟩ <;> obtain ⟨f, hf, h₀, h₁, h₂, h₃⟩ := key y <;> refine ⟨f, hf, ?_⟩
  · rw [← span_map, h₀]
  · simpa only [map_mul] using h₁ a b c d
  · rw [MvPolynomial.eval₂_comp_left, map_zero]; exact h₂ b F hF
  · rw [MvPolynomial.eval₂_comp_left, map_zero]; exact h₃ a F hF
end GlobalTheory.SegreCoord
