-- Prove2me | solution 1 for GlobalTheory.ChartJet.jS_pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:55.203824+00:00
-- url     : https://prove2.me/submissions/fb6735f5-7931-4f27-a77d-f3b9892dd14f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_pj_eq_mk
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
private theorem pj_add {κ : Type} [Finite κ] (m : ℕ) (g h : MvPowerSeries κ R) :
    pj m (g + h) = pj m g + pj m h := by
  simp only [pj, map_add]
private theorem pj_mul' {κ : Type} [Finite κ] (m : ℕ) (g h : MvPowerSeries κ R) :
    pj m (g * h) = pj m g * pj m h := by
  show pj m (g * h) = Ideal.Quotient.mk _ (truncTotal (m + 1) g) * Ideal.Quotient.mk _ (truncTotal (m + 1) h)
  rw [← map_mul, pj_eq_mk]
  intro x hx
  rw [MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]
private theorem pj_aeval (m : ℕ) (a : σ → MvPowerSeries τ R) (q : MvPolynomial σ R) :
    pj m (MvPolynomial.aeval a q) = MvPolynomial.aeval (fun s => pj m (a s)) q := by
  induction q using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    show pj m _ = Ideal.Quotient.mk _ (MvPolynomial.C r)
    rw [pj_eq_mk]
    intro e _
    classical
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
    by_cases h : e = 0
    · subst h
      simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  | add p q hp hq => rw [map_add, map_add, pj_add, hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, pj_mul', hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
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
theorem _root_.solution (m : ℕ) (a : σ → MvPowerSeries τ R) (ha) (f : MvPowerSeries σ R) : jS m a ha (pj m f) = pj m (subst a f) := by
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have h1 : pj m (subst a f) = pj m (subst a (truncTotal (m + 1) f : MvPowerSeries σ R)) := by
    show Ideal.Quotient.mk _ (truncTotal (m + 1) (subst a f)) =
      Ideal.Quotient.mk _ (truncTotal (m + 1) (subst a (truncTotal (m + 1) f : MvPowerSeries σ R)))
    rw [MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum ha' ha, ← MvPowerSeries.truncTotal_eq_sum]
  rw [h1, MvPowerSeries.subst_coe, pj_aeval]
  rfl
end GlobalTheory.ChartJet
