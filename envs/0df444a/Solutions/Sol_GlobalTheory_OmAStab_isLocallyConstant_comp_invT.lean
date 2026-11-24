-- Prove2me | solution 1 for GlobalTheory.OmAStab.isLocallyConstant_comp_invT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:03.077847+00:00
-- url     : https://prove2.me/submissions/21a41e99-770c-4c4d-8f3b-b486e4802538

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
import Theorems.Thm_GlobalTheory_OmAStab_continuous_invT_val
import Theorems.Thm_GlobalTheory_OmAStab_continuous_invT_inv_val
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM
open GlobalTheory GlobalTheory.OmAStab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.OmAStab
theorem _root_.solution {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    IsLocallyConstant fun h : GL D k => fun X : Matrix A D k => Φ (X * (invT h).val) := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
  set M : GL D k → Matrix D D k := fun h => (invT h).val with hM
  set N : GL D k → Matrix D D k := fun h => ((invT h)⁻¹).val with hN
  have hMc : Continuous M := continuous_invT_val
  have hNc : Continuous N := continuous_invT_inv_val
  have hMN : ∀ h, M h * N h = 1 := fun h => Units.mul_inv (invT h)
  have hNM : ∀ h, N h * M h = 1 := fun h => Units.inv_mul (invT h)
  have hq : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * M p.1) :=
    hl.comp_continuous (continuous_snd.matrix_mul (hMc.comp continuous_fst))
  have hr : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * N p.1 * M h0) :=
    hl.comp_continuous ((continuous_snd.matrix_mul (hNc.comp continuous_fst)).matrix_mul continuous_const)
  have hK1 : IsCompact ((fun Y => Y * N h0) '' tsupport Φ) :=
    hK.isCompact.image (continuous_id.matrix_mul continuous_const)
  have htend : ∀ X : Matrix A D k, Filter.Tendsto (fun p : GL D k × Matrix A D k => (h0, p.2))
      (𝓝 (h0, X)) (𝓝 (h0, X)) := fun X => (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
  have e1 : ∀ᶠ h in 𝓝 h0, ∀ X ∈ (fun Y => Y * N h0) '' tsupport Φ, Φ (X * M h) = Φ (X * M h0) := by
    refine hK1.eventually_forall_of_forall_eventually fun X _ => ?_
    have a1 := hq.eventually_eq (h0, X)
    have a2 := (htend X).eventually (hq.eventually_eq (h0, X))
    filter_upwards [a1, a2] with p hp1 hp2
    exact hp1.trans hp2.symm
  have e2 : ∀ᶠ h in 𝓝 h0, ∀ Y ∈ tsupport Φ, Φ (Y * N h * M h0) = Φ Y := by
    refine hK.isCompact.eventually_forall_of_forall_eventually fun Y _ => ?_
    have a2 := (continuous_snd.tendsto (h0, Y)).eventually (hl.eventually_eq Y)
    filter_upwards [hr.eventually_eq (h0, Y), a2] with p hp hp2
    refine hp.trans (Eq.trans ?_ hp2.symm)
    show Φ (Y * N h0 * M h0) = Φ Y
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  filter_upwards [e1, e2] with h h1 h2
  funext X
  show Φ (X * M h) = Φ (X * M h0)
  by_cases hA : X * M h0 ∈ tsupport Φ
  · exact h1 X ⟨X * M h0, hA, by simp only [Matrix.mul_assoc, hMN, Matrix.mul_one]⟩
  by_cases hB : X * M h ∈ tsupport Φ
  · have := h2 _ hB
    rw [Matrix.mul_assoc X, hMN, Matrix.mul_one] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]
end GlobalTheory.OmAStab
