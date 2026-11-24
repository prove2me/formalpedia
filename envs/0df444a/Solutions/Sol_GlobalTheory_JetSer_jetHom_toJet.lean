-- Prove2me | solution 1 for GlobalTheory.JetSer.jetHom_toJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:24:50.186543+00:00
-- url     : https://prove2.me/submissions/9e693b81-39b0-49b8-9e52-9a0f2ab42d64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Theorems.Thm_GlobalTheory_JetSer_toJet_eq_iff
import Theorems.Thm_GlobalTheory_JetSer_toJetHom_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}
variable [Finite κ]
namespace GlobalTheory.JetSer
theorem _root_.solution {σ : Type} [Finite σ] (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ)
    (ψ : JetR R σ m →ₐ[R] JetR R κ m) (hψ : ∀ j, ψ (zR m j) = toJet m (a j)) (g : MvPowerSeries σ R) :
    ψ (toJet m g) = toJet m (subst a g) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hpoly : ∀ Q : MvPolynomial σ R, ψ (Ideal.Quotient.mk _ Q) = toJet m (subst a (Q : MvPowerSeries σ R)) := by
    intro Q
    rw [subst_coe, ← toJetHom_apply]
    have : ψ.comp (Ideal.Quotient.mkₐ R _) = (toJetHom R κ m).comp (MvPolynomial.aeval a) := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, toJetHom_apply]
      exact hψ j
    exact AlgHom.congr_fun this Q
  refine (hpoly (truncTotal (m + 1) g)).trans ((toJet_eq_iff m _ _).2 fun e he => ?_)
  set r : MvPowerSeries σ R := (truncTotal (m + 1) g : MvPolynomial σ R) - g with hr
  have hro : ((m + 1 : ℕ) : ℕ∞) ≤ r.order := nat_le_order fun d hd => by
    rw [hr, map_sub, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite, if_pos hd, sub_self]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order := le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha i)
  have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (subst a r).order := by
    refine le_trans ?_ (le_order_subst hs r)
    calc ((m + 1 : ℕ) : ℕ∞) = 1 * ((m + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hro
  have h3 : coeff e (subst a r) = 0 := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast he) h2)
  rwa [hr, ← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply, substAlgHom_apply] at h3
end GlobalTheory.JetSer
