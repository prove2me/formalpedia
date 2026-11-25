-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.SphLaw.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:42:47.29029+00:00
-- url     : https://prove2.me/submissions/e096dfc3-76b7-4aac-bd73-40667bd9f841

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_wt_mul
import Theorems.Thm_GlobalTheory_T_generalLinear_integral_compact_open
import Theorems.Thm_GlobalTheory_T_iwasawa_decomposition_upperTriangular
import Theorems.Thm_GlobalTheory_T_localField_uniformizer_norm_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.SphLaw
namespace GlobalTheory.CompanionTheory.QL.SphLaw
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → (∀ k ∈ GLint O c, φ k = 1) ∧ (∀ g, ∀ k ∈ GLint O c, φ (g * k) = φ g) ∧ (∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ g, φ (b * g) = φ b * φ g) ∧ Continuous φ ∧ ∀ φ', IsSphFn O nrm χ φ' → φ' = φ := by
  intro F _ _ _ _ O ϖ nrm q hLF c χ α hU φ hφ
  obtain ⟨hq, -, -, -, hv', -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) := fun x hx =>
    (hv' x hx).imp fun _ h => h.1
  have hIw := (GlobalTheory.T.iwasawa_decomposition_upperTriangular hLF) c
  have hKo : IsOpen (GLint O c : Set (GL (Fin c) F)) := (GlobalTheory.T.generalLinear_integral_compact_open hLF c).1
  have hval : ∀ (ψ : GL (Fin c) F → ℂ), IsSphFn O nrm χ ψ → ∀ b : GL (Fin c) F,
      (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ k ∈ GLint O c,
      ψ (b * k) = wt nrm χ (b : Matrix (Fin c) (Fin c) F) := fun ψ hψ b hb k hk => hψ b hb k hk
  have hone : (1 : GL (Fin c) F) ∈ GLint O c := one_mem _
  have h1t : ((1 : GL (Fin c) F) : Matrix (Fin c) (Fin c) F).BlockTriangular id := by
    simpa using (Matrix.blockTriangular_one (b := (id : Fin c → Fin c)) (R := F))
  have hb1 : ∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id →
      φ b = wt nrm χ (b : Matrix (Fin c) (Fin c) F) := fun b hb => by
    simpa using hval φ hφ b hb 1 hone
  have hχ1 : ∀ i, χ i 1 = 1 := fun i => by
    have := hU.2 i 1 0 (by simp)
    simpa using this
  have hright : ∀ g, ∀ k ∈ GLint O c, φ (g * k) = φ g := by
    intro g k hk
    obtain ⟨b, hb, k', hk', rfl⟩ := hIw g
    rw [mul_assoc, hval φ hφ b hb _ ((GLint O c).mul_mem hk' hk), hval φ hφ b hb _ hk']
  refine ⟨?_, hright, ?_, ?_, ?_⟩
  · intro k hk
    have := hval φ hφ 1 h1t k hk
    rw [one_mul] at this
    rw [this]
    simp [wt, hχ1]
  · intro b hb g
    obtain ⟨b', hb', k, hk, rfl⟩ := hIw g
    have hbb : ((b * b' : GL (Fin c) F) : Matrix (Fin c) (Fin c) F).BlockTriangular id := by
      rw [Units.val_mul]; exact hb.mul hb'
    rw [← mul_assoc, hval φ hφ _ hbb k hk, hval φ hφ b' hb' k hk, hb1 b hb,
      wt_mul hq hv hU b b' hb hb']
  · refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (GLint O c : Set (GL (Fin c) F)),
      hKo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp [one_mem]
    · intro x hx
      have := hright g _ hx
      simpa using this
  · intro φ' hφ'
    funext g
    obtain ⟨b, hb, k, hk, rfl⟩ := hIw g
    rw [hval φ' hφ' b hb k hk, hval φ hφ b hb k hk]
end GlobalTheory.CompanionTheory.QL.SphLaw
