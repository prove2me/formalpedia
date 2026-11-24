-- Prove2me | solution 1 for GlobalTheory.IndexCol.mem_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:01.989813+00:00
-- url     : https://prove2.me/submissions/76f503f7-4fea-46e4-838d-da84a4c91856

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
import Theorems.Thm_GlobalTheory_IndexCol_conj_integral_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.IndexCol
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) {z : GL ι k} (hz : z ∈ KO k ι) :
    z ∈ (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom ↔
      (∀ r, r ≠ t → valuation k (z.val r t) < 1) ∧ ∀ r, r ≠ t → valuation k ((z⁻¹).val r t) < 1 := by
  set g := diagGL (Pi.mulSingle t ϖ : ι → kˣ) with hg
  have e : z ∈ (KO k ι).map (MulAut.conj g⁻¹).toMonoidHom ↔ g * z * g⁻¹ ∈ KO k ι := by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  obtain ⟨h1, h2⟩ := (mem_KO_iff z).1 hz
  have ev : (g * z * g⁻¹).val = g.val * z.val * (g⁻¹).val := by simp only [Units.val_mul]
  have ei : ((g * z * g⁻¹)⁻¹).val = g.val * (z⁻¹).val * (g⁻¹).val := by
    rw [show (g * z * g⁻¹)⁻¹ = g * z⁻¹ * g⁻¹ by group]; simp only [Units.val_mul]
  rw [e, mem_KO_iff, ev, ei, hg, conj_integral_iff hϖ t _ h1, conj_integral_iff hϖ t _ h2]
end GlobalTheory.IndexCol
