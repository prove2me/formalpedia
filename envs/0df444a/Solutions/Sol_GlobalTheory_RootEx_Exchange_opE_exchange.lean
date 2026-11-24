-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.opE_exchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:58.661264+00:00
-- url     : https://prove2.me/submissions/5f703ecd-3633-4e22-baf7-77a9f7ce7578

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_integral_glue
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_colE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_mat
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_big
import Theorems.Thm_GlobalTheory_RootEx_Exchange_hasCompactSupport_big
import Theorems.Thm_GlobalTheory_RootEx_Exchange_row_mul_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_col_colE_inv_mul
import Theorems.Thm_GlobalTheory_RootEx_Exchange_opE_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_opE_colE
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
open Classical
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x₀ : Matrix n n' k, (∀ χ : (n' → k) → ℂ, IsLocallyConstant χ → HasCompactSupport (fun u : n' → k => opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ) x₀) ∧ HasCompactSupport (fun β : n → k => opE ψ ν (p + 1) (om μ 1 (colE c (p + 1) β) Φ) x₀) ∧ ∫ u : n' → k, χ u * opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ) x₀ ∂(Measure.pi fun _ => ν) = ∫ β : n → k, opE ψ ν (p + 1) (fun x => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => x (Sum.inr l) (Sum.inl s)) else 0) * om μ 1 (colE c (p + 1) β) Φ x) x₀ ∂(Measure.pi fun _ => ν)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ ν _ μ Φ hΦ x₀ χ hχ
  haveI := t2Space k
  haveI := secondCountable k
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨q', hq⟩ : ∃ q' : Fin c, q.val + 1 = q'.val := ⟨⟨_, hpc⟩, rfl⟩
  have hΦ1 : Continuous Φ := hΦ.1.continuous
  have hΦ2 : HasCompactSupport Φ := hΦ.2
  refine ⟨?_, ?_, ?_⟩
  · refine HasCompactSupport.intro
      (K := (fun (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (s : n') => x (Sum.inr q) (Sum.inl s)) '' tsupport Φ)
      (hΦ2.isCompact.image (continuous_pi fun i => continuous_id.matrix_elem _ _)) fun u hu => ?_
    unfold opE
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
    have : Φ (affPt (q.val + 1) x₀ e * (rowE (c + 1) (q.val + 1) u).val) = 0 := by
      by_contra h
      exact hu ⟨_, subset_tsupport _ h, row_mul_rowE q u x₀ e⟩
    simp [om_rowE, this]
  · rw [hq]
    refine HasCompactSupport.intro
      (K := (fun (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r : n) =>
        -x (Sum.inl r) (Sum.inr q'.castSucc)) '' tsupport Φ)
      (hΦ2.isCompact.image (continuous_pi fun i => (continuous_id.matrix_elem _ _).neg)) fun β hβ => ?_
    unfold opE
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
    have : Φ (((colE c (q'.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * affPt (q'.val + 1) x₀ e) = 0 := by
      by_contra h
      exact hβ ⟨_, subset_tsupport _ h, col_colE_inv_mul q' β x₀ e⟩
    simp only [om_colE, this, zero_mul, Pi.zero_apply]
  · have hsum : ∀ x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
        (∑ l : Fin c, if l.val + 1 = q.val + 1 then χ (fun s => x (Sum.inr l) (Sum.inl s)) else 0) =
          χ (fun s => x (Sum.inr q) (Sum.inl s)) := by
      intro x
      simp [Fin.val_inj]
    simp only [hsum, opE_rowE hψ ν μ q hχ.continuous hΦ1]
    rw [hq]
    simp only [opE_colE hψ ν μ q q' hχ.continuous hΦ1]
    have hf := (continuous_big hψ q hχ.continuous hΦ1).comp (continuous_mat x₀)
    have hc := hasCompactSupport_big ψ q χ hΦ2 x₀
    let Q : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop := fun i => Free q'.val i ∨ Free (q'.val + 1) i
    have h1 := integral_glue ν (Free q'.val) Q (fun s : n' => (Sum.inr q, Sum.inl s))
      (fun a b h => by simpa using h) (fun s => by simp [Free, hq]) (by
        rintro ⟨r | r, s | s⟩ <;> simp [Q, Free, Fin.ext_iff, ← hq] <;> omega)
      (gRow q) (fun u s => by simp [gRow]) (by
        rintro u ⟨r | r, s | s⟩ h <;> simp [gRow]
        rintro rfl
        exact absurd rfl (h s)) _ hf hc
    have h2 := integral_glue ν (Free (q'.val + 1)) Q (fun r : n => (Sum.inl r, Sum.inr q'.castSucc))
      (fun a b h => by simpa using h) (fun s => by simp [Free]) (by
        rintro ⟨r | r, s | s⟩ <;> simp [Q, Free, Fin.ext_iff, ← hq] <;> omega)
      (gCol q') (fun u s => by simp [gCol]) (by
        rintro u ⟨r | r, s | s⟩ h <;> simp [gCol]
        rintro rfl
        exact absurd rfl (h r)) _ hf hc
    haveI : ν.Regular := Measure.regular_of_isAddLeftInvariant (isCompact_int k)
      (by rw [(isOpen_int k).interior_eq]; exact ⟨0, zero_mem _⟩) (isCompact_int k).measure_ne_top
    haveI : ν.IsNegInvariant := inferInstance
    refine Eq.trans ?_ (integral_neg_eq_self (fun β : n → k => ∫ e, big ψ q χ Φ
      (mat x₀ (ext0 (Free (q'.val + 1)) e + gCol q' β)) ∂(Measure.pi fun _ => ν)) _).symm
    exact h1.trans h2.symm
end GlobalTheory.RootEx.Exchange
