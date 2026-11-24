-- Prove2me | solution 1 for GlobalTheory.LocalInv.matches_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:50.873939+00:00
-- url     : https://prove2.me/submissions/f4e7c3d4-7ac3-40ae-84d1-a39f7f3e73a0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_eventually_out
import Theorems.Thm_GlobalTheory_LocalInv_chi_apply
import Theorems.Thm_GlobalTheory_LocalInv_iota_eps
import Theorems.Thm_GlobalTheory_LocalInv_galPol_tw_sum
import Theorems.Thm_GlobalTheory_LocalInv_galPol_speh
import Theorems.Thm_GlobalTheory_LocalInv_galPol_block
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    (hB : IsBCV N A i P (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (hρ : IsRankPart N i x ρ) :
    Matches N A i ρ (A.tw π A.etaTinv) ((1 - (R.nV : ℝ)) / 2) := by
  filter_upwards [eventually_out N i, A.locG_unr_ae (A.tw π A.etaTinv)] with w hw hu hs B σ hBw hσ
  have hw := hw hs
  have e1 := congrArg (Polynomial.map (iotaO N A i)) (hρ.2.2 w hw B σ hBw hσ)
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have e3 := hB.2.2.2.1 w hs
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, Polynomial.map_mul,
    Polynomial.map_prod] at e1
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  have hne : (∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact X_sub_C_ne_zero _
  rw [← e5] at e1
  have := mul_right_cancel₀ hne e1
  simpa using this
end GlobalTheory.LocalInv
