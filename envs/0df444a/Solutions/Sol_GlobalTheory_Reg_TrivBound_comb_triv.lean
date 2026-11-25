-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.comb_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:10.161481+00:00
-- url     : https://prove2.me/submissions/1732eb33-48ed-428b-9973-30125717aea0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
import Theorems.Thm_GlobalTheory_Reg_TrivBound_vV_unit
import Theorems.Thm_GlobalTheory_Reg_TrivBound_comb_core
import Theorems.Thm_GlobalTheory_Reg_TrivBound_chval_ne_bot
import Theorems.Thm_GlobalTheory_Reg_TrivBound_fin_of_ne_top
import Theorems.Thm_GlobalTheory_Reg_TrivBound_chval_zero
import Theorems.Thm_GlobalTheory_Reg_TrivBound_ratio_ge
import Theorems.Thm_GlobalTheory_Reg_TrivBound_w_fin
import Theorems.Thm_GlobalTheory_Reg_TrivBound_limit_triv
import Theorems.Thm_GlobalTheory_Reg_TrivBound_nonneg_triv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 1000000
namespace GlobalTheory.Reg.TrivBound
theorem _root_.solution {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL)
    {aE nE} {et : Rul Xo c} (het : et ∈ sec Xo c aE nE)
    (nu c' : ℝ) (hc' : 0 ≤ c')
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
      (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et)) :
    ∀ q ∈ trivSet Xo c, q et ≠ ⊤ → (⨅ k, q (ws k)) ≤ (c' : EReal) * q et := by
  intro q hq hT
  obtain ⟨kj, hkj⟩ := hF
  obtain ⟨j, V, _, _, _, _, φ, hcen, hunit, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have heO : 0 < S.eO := S.overO.1
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  have hu := hunit ϖ hϖ
  have hϖ0 : algebraMap S.O V ϖ ≠ 0 := hu.ne_zero
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
    have := nonneg_triv S hQ het (fun v' hv' => (hyp v' hv').1) q hq
    rw [ht] at this
    exact_mod_cast this
  have hκ : vr 1 (algebraMap S.O V ϖ) = 0 := by
    unfold vr
    rw [vV_unit _ (fun h => (IsLocalRing.mem_maximalIdeal _).1 h hu)]
    simp
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    have hm : maximalIdeal S.O = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
    exact hcen ϖ hϖ
  have key : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(N : ℝ) * c'⌉₊ : ℝ) * t := by
    intro N _
    have := comb_core ϖ S.eO heO (S.ch j (ws (kj j))) (S.ch j et) hfw0 x hx0 ye hye0 te hye yw tw hyw
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
      V φ hφx hϖ0 hqq 1 w t (hw ▸ hWc) (ht ▸ hTc)
    rw [hκ, mul_zero, zero_add] at this
    exact this
  have hlim := limit_triv w t c' ht0 hc' key
  calc (⨅ k, q (ws k)) ≤ q (ws (kj j)) := iInf_le _ _
    _ = (w : EReal) := hw
    _ ≤ ((c' * t : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hlim
    _ = (c' : EReal) * q et := by rw [ht, EReal.coe_mul]
end GlobalTheory.Reg.TrivBound
