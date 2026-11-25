-- Prove2me | solution 1 for GlobalTheory.LocalInv.not_subOrQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:00:46.594351+00:00
-- url     : https://prove2.me/submissions/70316497-b275-4e52-a039-13a04be86be8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_one_lt_normV
import Theorems.Thm_GlobalTheory_LocalInv_norm_cpow
import Theorems.Thm_GlobalTheory_LocalInv_r_odd
import Theorems.Thm_GlobalTheory_LocalInv_r_add_le
import Theorems.Thm_GlobalTheory_LocalInv_charRep_cont
import Theorems.Thm_GlobalTheory_LocalInv_charRep_ss
import Theorems.Thm_GlobalTheory_LocalInv_eps_cont
import Theorems.Thm_GlobalTheory_LocalInv_eig_mem
import Theorems.Thm_GlobalTheory_LocalInv_matches_chi
import Theorems.Thm_GlobalTheory_LocalInv_matches_rho
import Theorems.Thm_GlobalTheory_LocalInv_part_alg
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_ReciprocityTheory_Gal_exists_isFrob
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
theorem _root_.solution (eig : Eig N A) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered N A) (hLG : LocalGlobal N A)
    (hL : EigLaws N A eig) (hA : EigAway N A eig) (hAb : EigAbove N A eig) (hS : TemperedSizes N A eig)
    (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (x : N.X i) (π : A.CG R.r)
    (hx : HasParamX N A i x [⟨R.r, π, 1⟩]) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (hρ : IsRankPart N i x ρ) (w : PlE H) (j : ℕ) :
    ¬ SubOrQuot N i ρ (N.chi i 1 * eps N i ^ j) w := by
  intro hs
  obtain ⟨P, hP, hB⟩ := hx
  obtain ⟨σ, hσ⟩ : ∃ σ, FrobLift N w σ := exists_isFrob (N.plOm.2 w)
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  have hrt := r_add_le R
  have a1 := part_alg N A hη hW i P _ hB ⟨R.r, A.tw π A.etaTinv, 1⟩ (by simp [twistIso]) (r_odd R) odd_one
  have a2 := part_alg N A hη hW i P _ hB ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ (by simp [twistIso, muPart])
    odd_one R.t_odd

  have x1 : (1 - (R.nV : ℝ)) / 2 = -(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l1 := hLG i R.r (r_odd R).pos (A.tw π A.etaTinv) A.etaT (-(R.t : ℝ) / 2) a1.1 a1.2
    (fun τ z hz => by
      obtain ⟨k, hk⟩ := hη.2 τ z hz
      refine ⟨-t - 1 - k, ?_⟩
      rw [hk, ht]; push_cast; ring)
    ρ hρ.1 hρ.2.1 (x1 ▸ matches_rho N A i x π P hP hB ρ hρ) w

  have hc : Cont N i (charRep N i (N.chi i 1 * eps N i ^ j)) := by
    refine charRep_cont N i _ ?_
    refine ((N.chi_cont i 1).mul ((eps_cont N i).pow j)).congr fun g => ?_
    simp
  have x2 : ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + j =
      (-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l2 := hLG i 1 le_rfl (A.tw (A.muC i) A.etaTinv) A.etaT (-(R.r : ℝ) / 2 + j) a2.1 a2.2
    (fun τ z hz => by
      obtain ⟨k, hk⟩ := hη.2 τ z hz
      refine ⟨-r - 1 - k + j, ?_⟩
      rw [hk, hr]; push_cast; ring)
    _ hc (charRep_ss N i _) (x2 ▸ matches_chi N A i j) w
  obtain ⟨c1, c2, c3⟩ := hL w σ hσ
  obtain ⟨m, hm⟩ := Multiset.card_eq_one.mp
    ((c1 (A.locG (A.tw (A.muC i) A.etaTinv) w)).trans (A.locG_dim _ w))
  obtain ⟨c, hcc⟩ := Multiset.card_eq_one.mp ((c1 (A.locG A.etaT w)).trans (A.locG_dim _ w))
  have hmem := eig_mem N A eig hA hAb i ρ _ hρ.1 hc w l1.2 l2.2 hs σ hσ _
    (by rw [l2.1, c2, hm, Multiset.map_singleton])
  rw [l1.1, c2] at hmem
  obtain ⟨α, hα, he⟩ := Multiset.mem_map.mp hmem

  have s1 := (hS w σ hσ _ (hT _ (r_odd R).pos _ a1.1 a1.2 w) (α * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc]
    exact Multiset.mem_map_of_mem _ hα)).2
  have s2 := (hS w σ hσ _ (hT _ le_rfl _ a2.1 a2.2 w) (m * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc, hm]
    simp)).1
  rw [A.locG_dim] at s1 s2
  have hq := one_lt_normV w
  have hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ) := lt_trans one_pos hq
  have s2' : 1 ≤ ‖m * c‖ := by simpa using s2
  have hn : ‖α * c‖ * ((normV w : ℕ) : ℝ) ^ (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2) =
      ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) := by
    rw [← norm_cpow w, ← norm_cpow w, ← norm_mul, ← norm_mul]
    congr 1
    linear_combination c * he
  have hle : ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) ≤
      ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2 + (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2)) := by
    rw [Real.rpow_add hq0 (((R.r : ℝ) - 1) / 2)]
    calc _ ≤ ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hq0.le _) s2'
      _ = _ := hn.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right s1 (Real.rpow_nonneg hq0.le _)
  rw [Real.rpow_le_rpow_left_iff hq] at hle
  have h1 : (R.r : ℝ) + 5 ≤ R.t := by exact_mod_cast hrt
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hle
  linarith
end GlobalTheory.LocalInv
