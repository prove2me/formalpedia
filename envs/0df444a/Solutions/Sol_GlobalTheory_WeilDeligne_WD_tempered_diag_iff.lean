-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.tempered_diag_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:02.397702+00:00
-- url     : https://prove2.me/submissions/669da370-27b3-42a0-9571-2e5eb1518ca2

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
import Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_Tempered_norm_eq_one
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_mem_absSpace_diagEnd
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
theorem _root_.solution {ι : Type*} [Finite ι] (c : ι → ℂˣ) :
    (WDRep.diag h c).Tempered ↔ ∀ i, ‖(c i : ℂ)‖ = 1 := by
  classical
  constructor
  · intro ht i
    have h1 := ht.norm_eq_one rfl deg_frob
    have h2 : (Pi.single i 1 : ι → ℂ) ∈ absSpace ((WDRep.diag h c).ρ (frob h)) 1 := by
      rw [h1]; trivial
    rw [WDRep.diag_ρ, mem_absSpace_diagEnd] at h2
    by_contra hc
    simpa using h2 i (by simpa using hc)
  · intro hc φ hφ
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    have hz : ∀ (s : ℝ), s ≠ 0 → ∀ v ∈ absSpace ((WDRep.diag h c).ρ φ) (((normV w : ℕ) : ℝ) ^ s),
        v = 0 := by
      intro s hs v hv
      rw [WDRep.diag_ρ, mem_absSpace_diagEnd] at hv
      funext i
      refine hv i ?_
      rw [hφ, zpow_one, hc, ← Real.rpow_zero ((normV w : ℕ) : ℝ), Ne,
        Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne']
      exact hs.symm
    refine ⟨eq_top_iff.mpr fun v _ => Submodule.mem_iSup_of_mem 0 ?_, fun i => ?_⟩
    · rw [WDRep.diag_ρ, mem_absSpace_diagEnd]
      intro i hi
      exact absurd (by simp [hφ, hc]) hi
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp only [pow_zero, Nat.cast_zero, neg_zero]
        exact Set.bijOn_id _
      · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
        refine ⟨fun v hv => ?_, fun v hv v' hv' _ => ?_, fun v hv => ⟨0, zero_mem _, ?_⟩⟩
        · rw [hz _ (by linarith) v hv, map_zero]; exact zero_mem _
        · rw [hz _ (by linarith) v hv, hz _ (by linarith) v' hv']
        · rw [hz _ (by linarith) v hv, map_zero]
end GlobalTheory.WeilDeligne.WD
