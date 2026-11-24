-- Prove2me | solution 1 for GlobalTheory.Ex.twist_tx_ev_eq_map_arc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:55.442216+00:00
-- url     : https://prove2.me/submissions/d713b123-edc0-42d4-a48b-8ea7666c7dd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumMapPowerSeriesMkFinsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTxEvEqMapArc
import Theorems.Thm_GlobalTheory_Ex_hasSum_zpow_of_form_le
import Theorems.Thm_GlobalTheory_Ex_form_le_exponent
import Theorems.Thm_GlobalTheory_T_hom_transport_alt
import Theorems.Thm_GlobalTheory_T_twist_terms_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
namespace GlobalTheory.Ex
theorem _root_.solution : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 hX u hu N₀ N I k β₀ β hβ m hm hmo p₀ p hp1 hp2
  have hm0 : m ≠ 0 := hmo.pos.ne'
  have hT := (GlobalTheory.T.hom_transport_alt O C (φ.comp PowerSeries.C) N₀ N I).2.2.2.2 m hmo p₀ p hp1 hp2
  have hpt : ∀ χ₀ : N₀.X, p.1.1.toAdd + m • I.e χ₀ = I.e (p₀.1.1.toAdd + m • χ₀) := by
    intro χ₀
    rw [hp1, map_add, map_nsmul]
  have hdiv2 : ∀ x y, (2 * (m : ℤ) ^ 2) ∣ β₀.be x y := fun x y =>
    dvd_trans (mul_dvd_mul_left 2 (by exact_mod_cast hm)) (β₀.dvd x y)
  have hD2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  constructor
  · have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0 hD2
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2))
      (fun χ => (Int.mul_ediv_cancel' (hdiv2 _ _)).ge) (fun χ => N₀.txT m p₀ χ)
    have key : ∀ χ₀, (N.twist β u).txT m (N.twQ β u hm p) (I.e χ₀) =
        (I.lam : C) * (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2)) :
          Cˣ) : C) * φ (PowerSeries.C (N₀.txT m p₀ χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).1, hpt, hβ, (hT χ₀).1, RingHom.comp_apply]
      ring
    show ∑' χ, (N.twist β u).txT m (N.twQ β u hm p) χ = _
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f ((I.lam : C) * φ (N₀.arcTx β₀.be m p₀))) (funext key)).mpr
      (hsum.mul_left (I.lam : C))
  · intro j hj q₀ q hj0 hq1 hq2 s hs
    have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0
      (D := 4 * (m : ℤ) ^ 2) (by positivity)
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ) / j + s)
      (fun χ => form_le_exponent β₀ hm hj hj0 _ _ (s : ℤ) hs) (fun χ => N₀.evT m p₀ q₀.1.2 χ)
    have key : ∀ χ₀, (u : C) ^ s * (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 (I.e χ₀) =
        ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
          (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2) +
            β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ₀) / j + s) : Cˣ) : C) *
            φ (PowerSeries.C (N₀.evT m p₀ q₀.1.2 χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).2.1 j hj q hj0, hpt, hq1, hβ, hβ,
        (hT χ₀).2 q₀.1.2 q.1.2 hq2, RingHom.comp_apply]
      simp only [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    show (u : C) ^ s * ∑' χ, (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = _
    rw [← tsum_mul_left]
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f (((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
      φ (N₀.arcEv β₀.be m p₀ q₀ s))) (funext key)).mpr
      (hsum.mul_left ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C))
end GlobalTheory.Ex
