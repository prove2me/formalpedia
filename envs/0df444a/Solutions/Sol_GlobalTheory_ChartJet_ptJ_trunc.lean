-- Prove2me | solution 1 for GlobalTheory.ChartJet.ptJ_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:05.073179+00:00
-- url     : https://prove2.me/submissions/1e2df576-f4bf-4ad2-99e8-ba3a90ee69dc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_pj_trunc
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
variable {x} (hx : IsUnivChart G d x)
include hx
namespace GlobalTheory.ChartJet
theorem _root_.solution (m : ℕ) (p : Q R d n) : spMap (jetTruncR R _ m) ≫ ptJ x (m + 1) p = ptJ x m p := by
  have e : (jetTruncR R (Fin n × Fin d) m).comp (jP (m + 1) p) = (jP m p).comp (jetTruncR R (Fin d) m) := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    show jetTruncR R _ m (jP (m + 1) p (zR (m + 1) j)) = jP m p (jetTruncR R (Fin d) m (zR (m + 1) j))
    rw [jP_zR, pj_trunc]
    show pj m (p.1 j) = jP m p (zR m j)
    rw [jP_zR]
  unfold ptJ
  rw [← Category.assoc, ← jet_spMap_square_comm, e, jet_spMap_square_comm, Category.assoc, hx.1 m]
end GlobalTheory.ChartJet
