-- Prove2me | solution 1 for GlobalTheory.ChartJet.ptJ_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:03.83215+00:00
-- url     : https://prove2.me/submissions/a4b30c00-eeaa-44b3-8751-4296e83ed98a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_jS_pj
import Theorems.Thm_GlobalTheory_ChartJet_jP_zR
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


section
noncomputable section
namespace GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
section Points
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
end Points
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
private theorem jet_spMap_square_comm {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  apply Over.OverMorphism.ext
  simp only [spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp]
  rfl
private theorem jetR_algHom_ext_of_eq_on_zR {κ A : Type} [CommRing A] [Algebra R A] {m : ℕ} (f g : JetR R κ m →ₐ[R] A)
    (h : ∀ j, f (zR m j) = g (zR m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h
variable {x} (hx : IsUnivChart G d x)
include hx
end GlobalTheory.ChartJet
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
namespace GlobalTheory.ChartJet
theorem _root_.solution (m : ℕ) (b : Fin n → Q R d l) (p : Q R d n) : spMap (jQ m b) ≫ ptJ x m p = ptJ x m (sq b p) := by
  have e : (jQ m b).comp (jP m p) = jP m (sq b p) := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    show jQ m b (jP m p (zR m j)) = jP m (sq b p) (zR m j)
    rw [jP_zR, jP_zR]
    unfold jQ
    rw [jS_pj]
    show pj m (subst _ (p.1 j)) = pj m (sb b (p.1 j))
    rw [sb_apply]
    rfl
  unfold ptJ
  rw [← Category.assoc, ← jet_spMap_square_comm, e]
end GlobalTheory.ChartJet
