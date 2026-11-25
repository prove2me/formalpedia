-- Prove2me | solution 1 for GlobalTheory.ChartJet.exists_pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:53:30.011501+00:00
-- url     : https://prove2.me/submissions/8f00690e-488b-4c15-96a8-53209cc351c0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_pj_eq_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
private theorem coeff_add_degree_eq_coeff_degree_of_stable (q : ℕ → MvPolynomial σ R)
    (hq : ∀ m, ∀ e : σ →₀ ℕ, e.degree < m + 1 → (q (m + 1)).coeff e = (q m).coeff e)
    (e : σ →₀ ℕ) : ∀ j, (q (e.degree + j)).coeff e = (q e.degree).coeff e := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [← ih, ← Nat.add_assoc, hq _ e (by omega)]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
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
namespace GlobalTheory.ChartJet
theorem _root_.solution (z : ∀ m, JetR R σ m) (hz : ∀ m, jetTruncR R σ m (z (m + 1)) = z m) :
    ∃ f : MvPowerSeries σ R, ∀ m, pj m f = z m := by
  choose q hq using fun m => Ideal.Quotient.mk_surjective (z m)
  have hc : ∀ m, ∀ e : σ →₀ ℕ, e.degree < m + 1 → (q (m + 1)).coeff e = (q m).coeff e := by
    intro m e he
    have h := hz m
    rw [← hq (m + 1), ← hq m] at h
    have h' : (Ideal.Quotient.mk _ (q (m + 1)) : JetR R σ m) = Ideal.Quotient.mk _ (q m) := h
    rw [Ideal.Quotient.eq] at h'
    have := (MvPolynomial.mem_pow_idealOfVars_iff' _ _).1 h' e he
    rwa [MvPolynomial.coeff_sub, sub_eq_zero] at this
  refine ⟨(show MvPowerSeries σ R from fun e => (q e.degree).coeff e), fun m => ?_⟩
  rw [← hq m, pj_eq_mk]
  intro e he
  show (q e.degree).coeff e = (q m).coeff e
  obtain ⟨j, rfl⟩ : ∃ j, m = e.degree + j := ⟨m - e.degree, by omega⟩
  exact (coeff_add_degree_eq_coeff_degree_of_stable q hc e j).symm
end GlobalTheory.ChartJet
