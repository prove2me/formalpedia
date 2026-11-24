-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.translate_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:39.20961+00:00
-- url     : https://prove2.me/submissions/f8bfcb76-d596-4603-ae10-f9e7cb13b57b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_red_rowAdd
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_kerRed_eq
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_fill_add_single_of_notMem
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_mem_SB_mul_left
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_mem_itUp
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_mem_evAll
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_embA_tv_mul
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_embA_tv_inv_mul
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_ch_rowAdd
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_simpleSum_tv
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_embA_tv_mem
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_rowAdd_fill
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_OpenKernel_characters_locallyConstant
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
namespace GlobalTheory.FlatFactor.UpStage
section Gen
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
end Gen
section Pos
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)
variable {n n' c ρ}
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
private theorem addChar_comp_mul_mem_SB {X : Type} [TopologicalSpace X] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (f : X → k) (hf : Continuous f) (Θ : SB X) : (fun t => (ψ (f t) : ℂ) * Θ.1 t) ∈ SB X := by
  have hΘ : IsLocallyConstant Θ.1 ∧ HasCompactSupport Θ.1 := Θ.2
  exact ⟨(((GlobalTheory.RootEx.OpenKernel.characters_locallyConstant k).2 ψ hψ).comp_continuous hf).mul hΘ.1, hΘ.2.mul_left⟩
end Pos
end GlobalTheory.FlatFactor.UpStage
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)
variable {n n' c ρ}
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) [ν.IsAddHaarMeasure]
    {M : Type} [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hT : TwLaw ρ ψ L) (l j : Fin c) (hl : l.val < j.val) (hj : j.val < ρ)
    (hK : KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k)) L)
    (a : k) (Θ Θ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (h : ∀ t, Θ'.1 t = Θ.1 (t + Matrix.single (Sum.inr l) (Sum.inr j.castSucc) a)) : L Θ' = L Θ := by
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have hlj : l ≠ j := fun e => by rw [e] at hl; exact lt_irrefl _ hl
  have hsb : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 :=
    fun Φ => Φ.2
  have hnev : (Sum.inr l, Sum.inr j.castSucc) ∉ evAll n n' c ρ := by
    rw [mem_evAll]
    intro hc
    exact hc.1 (by simpa [Free] using hl)
  have hnit : (Sum.inr l, Sum.inr j.castSucc) ∉ itUp n n' c ρ (j.val + 1) := by
    rw [mem_itUp]
    rintro ⟨-, h2⟩
    rcases h2 _ rfl with h3 | h3 <;> simp at h3 <;> omega
  have hnit2 : (Sum.inr j, Sum.inr l.succ) ∉ itUp n n' c ρ (j.val + 1) := by
    rw [mem_itUp]
    rintro ⟨hf, -⟩
    simp only [Free, Fin.val_succ] at hf
    omega
  have hev2 : (Sum.inr j, Sum.inr l.succ) ∈ evAll n n' c ρ := by
    rw [mem_evAll]
    simp only [Free, IsRead, Fin.val_succ, not_false_eq_true, and_true]
    omega
  set u : GL (Fin c) k := tv l j hlj (-a) with hu
  have hmem : embA n u ∈ N k n c (ρ + 1) := embA_tv_mem l j hlj hl (-a) (ρ + 1)
  have hzero : ∀ i j' : Fin c, i.val < ρ → ρ ≤ j'.val → u.val i j' = 0 := by
    intro i j' hi hj'
    have h1 : i ≠ j' := fun e => by rw [e] at hi; omega
    have h2 : j ≠ j' := fun e => by rw [← e] at hj'; omega
    show (transvection l j (-a) : Matrix (Fin c) (Fin c) k) i j' = 0
    simp [transvection, Matrix.one_apply_ne h1, h2]
  let Θ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => Θ.1 (((embA n u)⁻¹).val * t), mem_SB_mul_left _ Θ⟩
  have hcoord : Continuous fun t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => -a * t (Sum.inr j) (Sum.inr l.succ) :=
    continuous_const.mul (continuous_id.matrix_elem (Sum.inr j) (Sum.inr l.succ))
  let Θ₂ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => (ψ (-a * t (Sum.inr j) (Sum.inr l.succ)) : ℂ) * Θ.1 t, addChar_comp_mul_mem_SB ψ hψ _ hcoord Θ⟩
  have hlaw : L Θ₁ = (ψ (-simpleSum (embA n u)) : ℂ) • L Θ₂ := by
    refine hT u hmem hzero Θ Θ₁ Θ₂ (fun t => rfl) (fun t => ?_)
    show (ψ (-a * t (Sum.inr j) (Sum.inr l.succ)) : ℂ) * Θ.1 t = _
    rw [hu, embA_tv_mul, ch_rowAdd]
  have h1 : L Θ₁ = L Θ' := by
    refine kerRed_eq ν _ _ _ L hK Θ₁ Θ' fun t => ?_
    have e1 : Θ₁.1 = fun x => Θ.1 (rowAdd (Sum.inr l) (Sum.inr j) a x) := by
      funext x
      show Θ.1 (((embA n (tv l j hlj (-a)))⁻¹).val * x) = _
      rw [embA_tv_inv_mul, neg_neg]
    rw [e1, red_rowAdd ν _ _ _ t (t + Matrix.single (Sum.inr l) (Sum.inr j.castSucc) a) (Sum.inr l) (Sum.inr j)
      (Sum.inr_injective.ne (Ne.symm hlj)) a Θ.1 (hsb Θ).1.continuous
      (fun α r q hrq => rowAdd_fill l j hl hj a t α r q hrq)]
    unfold red
    congr 1
    funext α
    rw [h, fill_add_single_of_notMem _ _ _ _ _ _ _ hnev hnit]
  have h2 : (ψ (-simpleSum (embA n u)) : ℂ) • L Θ₂ = L Θ := by
    rw [← map_smul]
    refine kerRed_eq ν _ _ _ L hK _ Θ fun t => ?_
    unfold red
    congr 1
    funext α
    have hfv : fill (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k)) t α (Sum.inr j) (Sum.inr l.succ)
        = if j.val = l.val + 1 then 1 else 0 := by
      simp only [fill, Matrix.of_apply]
      rw [dif_neg hnit2, if_pos hev2]
      simp [basePt]
    show (ψ (-simpleSum (embA n u)) : ℂ) * ((ψ (-a * _) : ℂ) * Θ.1 _) = Θ.1 _
    rw [← mul_assoc, hfv, hu, simpleSum_tv]
    split_ifs <;> simp [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  rw [← h1, hlaw, h2]
end GlobalTheory.FlatFactor.UpStage
