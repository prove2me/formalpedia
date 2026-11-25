-- Prove2me | solution 1 for GlobalTheory.ChartJet.ptJ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:52.166427+00:00
-- url     : https://prove2.me/submissions/e51598cf-63bb-4722-aba9-9ee34de445d7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
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
private theorem spMap_jetAug_comp_x_eq_one (m : ℕ) : spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
  have e : (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) = jetAug R (Fin d) m := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    rfl
  rw [← e, jet_spMap_square_comm, Category.assoc, hx.2.1 m, MonObj.comp_one]
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
variable {x} (hx : IsUnivChart G d x)
include hx
namespace GlobalTheory.ChartJet
theorem _root_.solution (m : ℕ) : ptJ x m (0 : Q R d n) = 1 := by
  have e : jP m (0 : Q R d n) = (Algebra.ofId R _).comp (jetAug R (Fin d) m) := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    rw [jP_zR]
    show pj m 0 = algebraMap R _ ((MvPolynomial.aeval fun _ => (0 : R)) (MvPolynomial.X j))
    rw [MvPolynomial.aeval_X, map_zero]
    simp [pj]
  unfold ptJ
  rw [e, jet_spMap_square_comm, Category.assoc, spMap_jetAug_comp_x_eq_one hx m, MonObj.comp_one]
end GlobalTheory.ChartJet
