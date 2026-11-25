-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WDRep.Tempered.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:49:28.577304+00:00
-- url     : https://prove2.me/submissions/21c6f8ab-9084-4b95-ac25-000f365e6213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply


attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
open GlobalTheory.WeilDeligne.WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne.WD
namespace _root_.GlobalTheory.WeilDeligne.WDRep.Tempered
theorem _root_.solution {a : WDRep h V} (ha : a.Tempered)
    (hN : a.N = 0) {φ : Weil h} (hφ : deg φ = 1) : absSpace (a.ρ φ) 1 = ⊤ := by
  obtain ⟨h1, h2⟩ := ha φ hφ
  rw [eq_top_iff, ← h1]
  refine iSup_le fun i v hv => ?_
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -((k + 1 : ℕ) : ℤ) := ⟨(-i - 1).toNat, by omega⟩
    have hv' : v ∈ absSpace (a.ρ φ) (((normV w : ℕ) : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2)) := by
      simpa using hv
    have := (h2 (k + 1)).2.1 hv' (zero_mem _) (by simp [hN])
    rw [this]; exact zero_mem _
  · simpa using hv
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = ((k + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
    have hv' : v ∈ absSpace (a.ρ φ) (((normV w : ℕ) : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2)) := by
      simpa using hv
    obtain ⟨u, -, hu⟩ := (h2 (k + 1)).2.2 hv'
    rw [← hu, hN]; simp
end _root_.GlobalTheory.WeilDeligne.WDRep.Tempered
end GlobalTheory.WeilDeligne.WD
