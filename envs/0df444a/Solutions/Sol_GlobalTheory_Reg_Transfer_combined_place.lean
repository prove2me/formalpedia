-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.combined_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:55.115835+00:00
-- url     : https://prove2.me/submissions/b4cf66c5-0dba-4007-bc12-9ec1c1127da8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentreChart
import Theorems.Thm_GlobalTheory_Reg_Transfer_integral_place
import Theorems.Thm_GlobalTheory_Reg_Transfer_vr_of_over
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_ne_bot
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_zero
import Theorems.Thm_GlobalTheory_Reg_Transfer_comb_core
import Theorems.Thm_GlobalTheory_Reg_Transfer_fin_of_ne_top
import Theorems.Thm_GlobalTheory_Reg_Transfer_limit_lam
import Theorems.Thm_GlobalTheory_Reg_Transfer_ratio_ge
import Theorems.Thm_GlobalTheory_Reg_Transfer_w_fin
import Theorems.Thm_P2M_GlobalTheory_Reg_Transfer_vV_zero__d1cc3821e421


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing NumberField IsDedekindDomain Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Reg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 1000000
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL)
    {aE nE} {et : Rul Xo c} (het : et ∈ sec Xo c aE nE)
    (nu c' : ℝ) (hc' : 0 ≤ c')
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
      (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et)) :
    ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et := by
  intro v hv hT
  obtain ⟨kj, hkj⟩ := hF
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, hϖv, hmap, hChV⟩ := S.cover v hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have he : 0 < e := hov.1
  have heO : 0 < S.eO := S.overO.1
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  have hϖ0 : algebraMap S.O V ϖ ≠ 0 := by
    intro h0
    have := hϖv ϖ hϖ
    rw [h0, map_zero, vV_zero', zero_mul] at this
    omega
  obtain ⟨hfw0, hrat, hinv⟩ := hkj j
  obtain ⟨yw, tw, hyw⟩ := hinv x hxE ϖ hϖ
  obtain ⟨ye, te, hye⟩ := S.reg j aE nE et het x hxE ϖ hϖ
  have hP : ∀ k : ℕ, φ ((algebraMap S.O (S.A j) ϖ * x) ^ k) ≠ 0 := fun k => by
    rw [map_pow, map_mul, AlgHom.commutes]; exact pow_ne_zero _ (mul_ne_zero hϖ0 hφx)
  have hWc := hChV aL nL (ws (kj j)) (hws _)
  have hTc := hChV aE nE et het
  obtain ⟨w, hw⟩ := w_fin hWc _ yw hyw hfw0 (hP tw)
  obtain ⟨t, ht⟩ := fin_of_ne_top hT (chval_ne_bot hTc)
  have hye0 : ye ≠ 0 := by
    rintro rfl
    rw [map_zero] at hye
    have hPK : algebraMap (S.A j) (FractionRing (S.A j)) ((algebraMap S.O (S.A j) ϖ * x) ^ te) ≠ 0 := by
      intro h0
      apply hP te
      rw [IsFractionRing.injective (S.A j) (FractionRing (S.A j)) (h0.trans (map_zero _).symm), map_zero]
    have hfe0 : S.ch j et = 0 := (mul_eq_zero.1 hye).resolve_right hPK
    rw [hfe0] at hTc
    exact hT (chval_zero hTc)
  have ht0 : 0 ≤ t := by
    have := integral_place S het (fun v' hv' => (hyp v' hv').1) v hv
    rw [ht] at this
    exact_mod_cast this
  have hκ : vr e (algebraMap S.O V ϖ) = 1 / S.eO := vr_of_over S.eO e heO he _ (hϖv ϖ hϖ)
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    rw [sup_eq_left.2 hmap]; exact Ideal.IsPrime.ne_top inferInstance
  have key : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤
      (⌈(S.eO : ℝ) * N * nu⌉ : ℝ) * (1 / S.eO) + (⌈(N : ℝ) * c'⌉₊ : ℝ) * t := by
    intro N _
    rw [← hκ]
    exact comb_core ϖ S.eO heO (S.ch j (ws (kj j))) (S.ch j et) hfw0 x hx0 ye hye0 te hye yw tw hyw
      nu c' N ⌈(S.eO : ℝ) * N * nu⌉ ⌈(N : ℝ) * c'⌉₊ (Int.le_ceil _) (Nat.le_ceil _)
      (fun V' _ _ _ _ _ φ' hφ'x => by
        obtain ⟨ioV', e', hov', hϖ', v', hv', hch'⟩ := S.pts j V' φ' ⟨x, hxE, hφ'x⟩
        refine ⟨e', v' (ws (kj j)), v' et, hov'.1, hϖ' ϖ hϖ, hch' aL nL _ (hws _),
          hch' aE nE et het, (hyp v' hv').1, fun hT' => ?_⟩
        refine le_trans (le_iInf fun k => ?_) ((hyp v' hv').2 hT')
        obtain ⟨xk, hxk⟩ := hrat k
        have h2 := hch' aL nL (ws k) (hws k)
        rw [hxk] at h2
        exact ratio_ge (hch' aL nL _ (hws _)) h2)
      V φ hφx hϖ0 hqq e w t (hw ▸ hWc) (ht ▸ hTc)
  have hlim := limit_lam w t nu c' S.eO heO ht0 hc' key
  calc (⨅ k, v (ws k)) ≤ v (ws (kj j)) := iInf_le _ _
    _ = (w : EReal) := hw
    _ ≤ ((nu + c' * t : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hlim
    _ = (nu : EReal) + (c' : EReal) * v et := by rw [ht, EReal.coe_add, EReal.coe_mul]
end GlobalTheory.Reg.Transfer
