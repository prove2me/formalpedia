-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_zero
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:49:29.604794+00:00
-- url     : https://prove2.me/submissions/a1d62fe4-cee8-4617-8060-b9a092d9e704

import Definitions.Def_HodgeComputerSSR_Q5K5Master
import Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_mvPoly3_eq_zero_of_kronecker2D_gridT
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_cache_rel
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_bounds
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_0
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_1
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_2
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_3
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_4
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_5
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_6
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_7
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_8
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_master_t_9

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.Q5WeightsData
  PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len

private abbrev evalSQCache_rel := @HodgeComputer.SymmetricSexticResidual.Proof.localQ5_cache_rel.2.2.1
private abbrev evalTStep_rel := @HodgeComputer.SymmetricSexticResidual.Proof.localQ5_cache_rel.2.2.2.2

private lemma master_values_ok : checkMasterTChunk (-9) 20 = true := by
  have h01 : checkMasterTChunk (-9) 4 = true := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_0, by rw [show (-9 : ℤ) + (2 : ℕ) = -7 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_1⟩
  have h02 : checkMasterTChunk (-9) 6 = true := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨h01, by rw [show (-9 : ℤ) + (4 : ℕ) = -5 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_2⟩
  have h03 : checkMasterTChunk (-9) 8 = true := by
    rw [show (8 : ℕ) = 6 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨h02, by rw [show (-9 : ℤ) + (6 : ℕ) = -3 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_3⟩
  have h04 : checkMasterTChunk (-9) 10 = true := by
    rw [show (10 : ℕ) = 8 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨h03, by rw [show (-9 : ℤ) + (8 : ℕ) = -1 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_4⟩
  have h05 : checkMasterTChunk (-9) 12 = true := by
    rw [show (12 : ℕ) = 10 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨h04, by rw [show (-9 : ℤ) + (10 : ℕ) = 1 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_5⟩
  have h06 : checkMasterTChunk (-9) 14 = true := by
    rw [show (14 : ℕ) = 12 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨h05, by rw [show (-9 : ℤ) + (12 : ℕ) = 3 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_6⟩
  have h07 : checkMasterTChunk (-9) 16 = true := by
    rw [show (16 : ℕ) = 14 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨h06, by rw [show (-9 : ℤ) + (14 : ℕ) = 5 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_7⟩
  have h08 : checkMasterTChunk (-9) 18 = true := by
    rw [show (18 : ℕ) = 16 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
    exact ⟨h07, by rw [show (-9 : ℤ) + (16 : ℕ) = 7 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_8⟩
  rw [show (20 : ℕ) = 18 + 2 from rfl, checkMasterTChunk_append, Bool.and_eq_true]
  exact ⟨h08, by rw [show (-9 : ℤ) + (18 : ℕ) = 9 from rfl]; exact HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_9⟩

private lemma master_bivL_zero_K5 :
    evalBivLK5 (evalTStep k5Ops S_K cacheK T_K) = 0 := by
  have hb_ok : checkMasterBounds = true := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_bounds
  have hv_ok : checkMasterTChunk (-9) 20 = true := master_values_ok
  unfold checkMasterBounds at hb_ok
  unfold checkMasterTChunk at hv_ok
  let cP3 := evalSQCache poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
  let bP3 := evalTStep poly3Ops (MvPolynomial.X 0) cP3 (MvPolynomial.X 2)
  let bPB := evalTStep pbOps ⟨1, 0, 0, 1⟩ cPB2D ⟨0, 0, 1, 10⟩
  have hrelB : BRel (RespectsBound2D masterDegS 10) bP3 bPB :=
    evalTStep_rel (respectsBound2DRel masterDegS 10) (respectsBound2D_X0 masterDegS 10)
      (evalSQCache_rel (respectsBound2DRel masterDegS 10) (respectsBound2D_X0 masterDegS 10) (respectsBound2D_X1 masterDegS 10))
      (respectsBound2D_X2 masterDegS 10)
  have hbQ_eq : ((masterLim ^ masterDegS : ℕ) : ℤ) = bQ2D := by
    have hpow : ∀ a b : ℕ, (((Nat.pow 2 a) ^ b : ℕ) : ℤ) = Int.ofNat (Nat.pow 2 (b * a)) := by
      intro a b; rw [show Nat.pow 2 a = 2 ^ a from rfl, ← pow_mul, Nat.mul_comm]; rfl
    unfold masterLim bQ2D
    exact hpow masterBits masterDegS
  have hrelV (t : ℤ) :
      BRel (fun p z => MvPolynomial.eval (v3Int (masterLim : ℤ) ((masterLim ^ masterDegS : ℕ) : ℤ) t) p = z)
        bP3 (evalTStep intOps bS2D c2D t) :=
    evalTStep_rel (poly3ToIntRel (masterLim : ℤ) ((masterLim ^ masterDegS : ℕ) : ℤ) t)
      (by rw [MvPolynomial.eval_X, v3Int]; rfl)
      (evalSQCache_rel (poly3ToIntRel (masterLim : ℤ) ((masterLim ^ masterDegS : ℕ) : ℤ) t)
        (by rw [MvPolynomial.eval_X, v3Int]; rfl) (by rw [MvPolynomial.eval_X, v3Int]; exact hbQ_eq))
      (by rw [MvPolynomial.eval_X, v3Int])
  have hrelK : BRel (fun p x => evalP3K5 p = x) bP3 (evalTStep k5Ops S_K cacheK T_K) :=
    evalTStep_rel poly3ToK5Rel (by simp [evalP3K5, v3K5])
      (evalSQCache_rel poly3ToK5Rel (by simp [evalP3K5, v3K5]) (by simp [evalP3K5, v3K5]))
      (by simp [evalP3K5, v3K5])
  have hallB : ∀ r ∈ bPB, ∀ b ∈ r, b.dS < masterDegS ∧ b.dT < 20 ∧ b.M < masterLim := by
    intro r hr b hb
    have h1 := List.all_eq_true.mp hb_ok r hr
    have h2 := List.all_eq_true.mp h1 b hb
    simp only [Bool.and_eq_true, Nat.blt_eq] at h2
    exact ⟨h2.1.1, h2.1.2, h2.2⟩
  have hallV : ∀ t ∈ rangeInt (-9) 20,
      ∀ r ∈ evalTStep intOps bS2D c2D t, ∀ z ∈ r, z = 0 := by
    intro t ht r hr z hz
    have h1 := allRange_spec (-9) 20 _ hv_ok t ht
    have h2 := List.all_eq_true.mp h1 r hr
    exact beq_iff_eq.mp (List.all_eq_true.mp h2 z hz)
  have hrow_zero : ∀ (D B : ℕ) (rP : UPoly P3Z) (rB : UPoly PB) (rV : ℤ → UPoly ℤ) (rK : UPoly K5),
      URel (RespectsBound2D D 10) rP rB →
      (∀ t, URel (fun p z => MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = z) rP (rV t)) →
      URel (fun p x => evalP3K5 p = x) rP rK →
      (∀ b ∈ rB, b.dS < D ∧ b.dT < 20 ∧ b.M < B) →
      (∀ t ∈ rangeInt (-9) 20, ∀ z ∈ rV t, z = 0) →
      evalYListK5 rK = 0 := by
    intro D B rP
    induction rP with
    | nil =>
        intro rB rV rK _ _ hrK _ _
        cases hrK; rfl
    | cons p ps ih =>
        intro rB rV rK hrB hrV hrK haB haV
        cases hrB with | cons hb hbs =>
        cases hrK with | cons hk hks =>
        rename_i b bs k ks
        obtain ⟨hdS, hdT, hM⟩ := haB b (by simp)
        have hp0 : p = 0 := by
          apply HodgeComputer.Formal.KroneckerCheck.mvPoly3_eq_zero_of_kronecker2D_gridT p b D 10 B (rangeInt (-9) 20)
            hb hdS (by rw [rangeInt_card]; exact hdT)
            (rangeInt_natAbs_le (-9) 20 10 (by decide) (by decide)) hM
          intro t ht
          have hvt := hrV t
          rcases hv : rV t with _ | ⟨z, zs⟩
          · rw [hv] at hvt; cases hvt
          · rw [hv] at hvt; cases hvt with | cons hz _ =>
            rw [hz]; exact haV t ht z (by simp [hv])
        have hk0 : k = 0 := by rw [← hk, hp0, map_zero]
        have htail0 : evalYListK5 ks = 0 := by
          apply ih bs (fun t => (rV t).tail) ks hbs
          · intro t
            have hvt := hrV t
            rcases hv : rV t with _ | ⟨z, zs⟩
            · rw [hv] at hvt; cases hvt
            · rw [hv] at hvt; cases hvt with | cons _ hzs => simpa [hv] using hzs
          · exact hks
          · intro x hx; exact haB x (by simp [hx])
          · intro t ht z hz
            rcases hv : rV t with _ | ⟨z0, zs⟩
            · simp [hv] at hz
            · simp only [hv, List.tail_cons] at hz
              exact haV t ht z (by simp [hv, hz])
        simp only [evalYListK5, evalYList, hk0, htail0, mul_zero, add_zero]
  have hzero_gen : ∀ (D B : ℕ) (bP : BivL P3Z) (bB : BivL PB)
      (bV : ℤ → BivL ℤ) (bK : BivL K5),
      BRel (RespectsBound2D D 10) bP bB →
      (∀ t, BRel (fun p z => MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = z) bP (bV t)) →
      BRel (fun p x => evalP3K5 p = x) bP bK →
      (∀ r ∈ bB, ∀ b ∈ r, b.dS < D ∧ b.dT < 20 ∧ b.M < B) →
      (∀ t ∈ rangeInt (-9) 20, ∀ r ∈ bV t, ∀ z ∈ r, z = 0) →
      evalBivLK5 bK = 0 := by
    intro D B bP
    induction bP with
    | nil =>
        intro bB bV bK _ _ hrK _ _
        cases hrK; rfl
    | cons r rs ih =>
        intro bB bV bK hrB hrV hrK haB haV
        cases hrB with | cons hrb hrbs =>
        cases hrK with | cons hrk hrks =>
        rename_i rB rBs rK rKs
        have hr0 : evalYListK5 rK = 0 := by
          apply hrow_zero D B r rB (fun t => (bV t).headD []) rK hrb
          · intro t
            have hvt := hrV t
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · rw [hv] at hvt; cases hvt
            · rw [hv] at hvt; cases hvt with | cons hrv _ => simpa [hv] using hrv
          · exact hrk
          · exact haB rB (by simp)
          · intro t ht z hz
            have hvt := hrV t
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · rw [hv] at hvt; cases hvt
            · simp only [hv, List.headD_cons] at hz
              exact haV t ht rv (by simp [hv]) z hz
        have htail0 : evalBivLK5 rKs = 0 := by
          apply ih rBs (fun t => (bV t).tail) rKs hrbs
          · intro t
            have hvt := hrV t
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · rw [hv] at hvt; cases hvt
            · rw [hv] at hvt; cases hvt with | cons _ hrvs => simpa [hv] using hrvs
          · exact hrks
          · intro r' hr'; exact haB r' (by simp [hr'])
          · intro t ht r' hr' z hz
            rcases hv : bV t with _ | ⟨rv, rvs⟩
            · simp [hv] at hr'
            · simp only [hv, List.tail_cons] at hr'
              exact haV t ht r' (by simp [hv, hr']) z hz
        simp only [evalBivLK5, evalBivL, hr0, htail0, mul_zero, add_zero]
  exact hzero_gen masterDegS masterLim bP3 bPB (evalTStep intOps bS2D c2D) (evalTStep k5Ops S_K cacheK T_K) hrelB hrelV hrelK hallB hallV


end SymmetricSexticResidual.LocalResidueQ5

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.evalBivLK5
      (SymmetricSexticResidual.LocalResidueQ5.evalTStep
        SymmetricSexticResidual.LocalResidueQ5.k5Ops
        SymmetricSexticResidual.K5Field.S_K
        SymmetricSexticResidual.LocalResidueQ5.cacheK
        SymmetricSexticResidual.K5Field.T_K) = 0 :=
  SymmetricSexticResidual.LocalResidueQ5.master_bivL_zero_K5
