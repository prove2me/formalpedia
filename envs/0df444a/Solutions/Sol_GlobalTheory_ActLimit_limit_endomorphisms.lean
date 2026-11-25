-- Prove2me | solution 1 for GlobalTheory.ActLimit.limit_endomorphisms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:27:06.916161+00:00
-- url     : https://prove2.me/submissions/2fc01ca6-2747-4eb9-8f37-a58a6323c8a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_Tends_unique
import Theorems.Thm_GlobalTheory_ActLimit_Tends_ge
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_const
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_sub
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_unique
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_subst
import Theorems.Thm_GlobalTheory_ActLimit_const_of_ev
import Theorems.Thm_GlobalTheory_ActLimit_const_pt
import Theorems.Thm_GlobalTheory_ActLimit_const_comp1
import Theorems.Thm_GlobalTheory_ActLimit_tends_comp1
import Theorems.Thm_GlobalTheory_ActLimit_constantCoeff_germEvalTwo_eq_zero
import Theorems.Thm_GlobalTheory_ActLimit_tendsToCoeffwise_germEvalTwo
import Theorems.Thm_GlobalTheory_ActLimit_exists_lim
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActLimit
variable {C : Type} [Field C] {V : VF C}
variable {dd : ℕ}
namespace GlobalTheory.ActLimit
theorem _root_.solution : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), EndomorphismLimitIntegral Y := by
  intro C _ _ V O _ _ dd Y a ha hb
  obtain ⟨e, he⟩ := exists_lim Y ha
  obtain ⟨eb, heb⟩ := exists_lim Y hb
  have hc := Y.B.A.const
  refine ⟨e, eb, fun i μ => (he i μ).ge fun n => Y.intAct _ i μ, fun i μ => (heb i μ).ge fun n => Y.intAct _ i μ,
    fun N i μ => eventually_atTop.1 (he i μ N), fun N i μ => eventually_atTop.1 (heb i μ N), ?_, ?_⟩
  · funext i
    have h1 := tends_comp1 he (a := addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1))
      (fun i => constantCoeff_germEvalTwo_eq_zero (const_pt 0) (const_pt 1) (Y.B.G.const i)) i
    have h2 := tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun k => const_comp1 (hc (a k)) (const_pt 1)) (tends_comp1 he (const_pt 0))
      (tends_comp1 he (const_pt 1)) (Y.B.G.F i)
    refine h1.unique ?_
    simp only [Y.B.A.hom]
    exact h2
  · have hh : MvPowerSeries.constantCoeff Y.h = 0 :=
      const_of_ev (fun j i => by fin_cases j; exacts [map_zero _, const_pt 0 i]) Y.gauge.ax0
    have hid : ∀ {τ : Type} (f : MvPowerSeries τ C), MvPowerSeries.map (algebraMap C C) f = f := fun f => by
      ext μ; simp
    have hK : ∀ x, Y.B.actK C x = Y.B.A.act x := fun x => funext fun i => hid _
    have h1 := (tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun _ => const_pt 1) (tends_comp1 he (const_pt 0)) (fun i => TendsS.const _) Y.h).sub
      (tendsToCoeffwise_germEvalTwo (V := V) (fun _ => const_pt (n := 2) 0) (fun k => const_comp1 (hc (star (a k))) (const_pt 1))
        (fun i => TendsS.const _) (tends_comp1 heb (const_pt 1)) Y.h)
    have h2 := TendsS.subst (σ := Unit) (fun k _ => by
      rw [map_sub, constantCoeff_germEvalTwo_eq_zero (const_comp1 (hc (a k)) (const_pt (n := 2) 0)) (const_pt 1) hh,
        constantCoeff_germEvalTwo_eq_zero (const_pt (n := 2) 0) (const_comp1 (hc (star (a k))) (const_pt 1)) hh, sub_zero])
      (fun _ => h1) (TendsS.const (PowerSeries.exp C))
    intro μ
    refine (h2 μ).ge fun n => ?_
    have h3 := Y.gauge.ad (a n)
    rw [hK, hK] at h3
    have h4 := Y.intAd (a n) μ
    rw [(hid (Y.B.ad (a n))).symm.trans h3] at h4
    exact h4
end GlobalTheory.ActLimit
