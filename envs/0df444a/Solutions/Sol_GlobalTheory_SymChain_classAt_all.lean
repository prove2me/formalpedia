-- Prove2me | solution 1 for GlobalTheory.SymChain.classAt_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:40.504262+00:00
-- url     : https://prove2.me/submissions/99a53635-d4e6-4b70-9fe9-51b6b4f60364

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPhiSupportPeriodicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainClassAtEveryPosition
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_blockTriangular_inv
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_exists_unip_mul_levi
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_opE_om_target_unipotent
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_stabLat
import Theorems.Thm_GlobalTheory_T_doubleBlockTriangular_mem_integral_mul_levi
import Theorems.Thm_GlobalTheory_T_rootExchange_blockDiagonal_target_entry_conditions
import Theorems.Thm_GlobalTheory_T_symmetricLevelChain_phi_support_periodic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain
namespace GlobalTheory.SymChain
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ j c H p hp1 hpc h hE
  haveI := hν.1
  obtain ⟨D, hDdef⟩ : ∃ D : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
      D = embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : GL (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      D' = embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  have hD : (S.T t).bas (j + 1) c (by omega) = D := by rw [hDdef]; rfl
  have hlt : valuation k (S.ϖ : k) < 1 := (S.unif (S.ϖ : k)).2 le_rfl
  let lv' : XIx (Fin κ) t (j + 1) ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))
  have hlv : ∀ r s, lev p s < lev p r → lv' s < lv' r := by
    rintro (r | r) (s | s) h0 <;> simp only [lev, lv', Sum.elim_inl, Sum.elim_inr] at h0 ⊢ <;> omega
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k _ lv' (h * D)
  have hb' : b.val.BlockTriangular (lev p) := fun r s hrs => hb (hlv r s hrs)
  obtain ⟨u, hu, m, hm1, hm2, hum⟩ := BlockLevi.exists_unip_mul_levi k _ c p b hb'
  have hh : h = u * (m * w * D⁻¹) := by
    have : h = h * D * D⁻¹ := by group
    rw [this, hbw, hum]; group
  obtain ⟨v, hv⟩ : ∃ v, v = m * w * D⁻¹ := ⟨_, rfl⟩
  rw [← hv] at hh
  have key : om (S.μ (j + 1)) 1 (u * v) ((S.T t).Phi j c H) =
      om (S.μ (j + 1)) 1 u (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) := by
    simpa using Model.om_mul (S.μ (j + 1)) 1 1 u v ((S.T t).Phi j c H)
  have hE' : opE S.ψ ν p (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0; apply hE
    rw [hh, key, opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν (S.μ (j + 1)) _ u hu, h0, smul_zero]
  have eg : D⁻¹ * v⁻¹ = w⁻¹ * m⁻¹ := by rw [hv]; group
  have ev : ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      (D⁻¹).val * ((v⁻¹).val * x) * D'.val = (w⁻¹).val * ((m⁻¹).val * x * D'.val) := by
    intro x
    rw [← Matrix.mul_assoc (D⁻¹).val, ← Units.val_mul, eg, Units.val_mul]; simp only [Matrix.mul_assoc]
  have hinst := GlobalTheory.T.symmetricLevelChain_phi_support_periodic k s κ S t j c H
  rw [← hDdef, ← hD'def] at hinst
  have hsup : ∀ x, om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x ≠ 0 → IntM ((m⁻¹).val * x * D'.val) := by
    intro x hx
    have hΦ : (S.T t).Phi j c H ((v⁻¹).val * x) ≠ 0 := by
      have := right_ne_zero_of_mul hx
      simpa using this
    have h1 := (hinst ((v⁻¹).val * x) 0).1 hΦ
    rw [ev] at h1
    have e2 : (m⁻¹).val * x * D'.val = w.val * ((w⁻¹).val * ((m⁻¹).val * x * D'.val)) := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e2]; exact (intM_of_mem_KO hw).mul h1
  have hper : ∀ x z, MaxM ((m⁻¹).val * z * D'.val) →
      om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) (x + z) = om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x := by
    intro x z hz
    have h1 : MaxM ((D⁻¹).val * ((v⁻¹).val * z) * D'.val) := by
      rw [ev]; exact (mem_KO.1 hw).2.mul_maxM hz
    simp only [om, Units.val_one, Matrix.mul_one, Matrix.mul_add]
    rw [(hinst ((v⁻¹).val * x) ((v⁻¹).val * z)).2 h1]
  have sm1 : m.val.BlockTriangular lv' := by
    intro r s hrs
    by_cases e : lev p r = lev p s
    · rw [hm2 r s e]; exact hb hrs
    · exact hm1 r s e
  have sm2 : m.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    intro r s hrs
    exact hm1 r s (Nat.ne_of_lt (OrderDual.toDual_lt_toDual.mp hrs))
  have si1 : (m⁻¹).val.BlockTriangular lv' := BlockLevi.blockTriangular_inv lv' m sm1
  have si2 : (m⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    letI : Invertible m.val := m.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular sm2
  have sm1' : (m⁻¹⁻¹).val.BlockTriangular lv' := by rw [inv_inv]; exact sm1
  have sm2' : (m⁻¹⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by rw [inv_inv]; exact sm2
  rw [hD'def] at hsup hper
  obtain ⟨E1, E2⟩ := GlobalTheory.T.rootExchange_blockDiagonal_target_entry_conditions k S.ψ ν S.cond S.ϖ hlt _ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' _ hsup hper hE'
  obtain ⟨γ, hK⟩ := GlobalTheory.T.doubleBlockTriangular_mem_integral_mul_levi k S.ϖ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' E1 E2
  rw [← hDdef] at hK
  refine ⟨u * embX c γ, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨γ, rfl⟩),
    (u * embX c γ)⁻¹ * h, ?_, by group⟩
  rw [hD, mem_stabLat]
  have : D⁻¹ * ((u * embX c γ)⁻¹ * h) * D = (m⁻¹ * embX c γ * D)⁻¹ * w := by
    rw [hh, hv]; group
  rw [this]
  exact mul_mem (inv_mem hK) hw
end GlobalTheory.SymChain
