-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerAdj.entry_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:03:19.245637+00:00
-- url     : https://prove2.me/submissions/c2cf9a41-6093-4441-a786-6f2b0e427f68

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerEqIntegralConjMul
import Theorems.Thm_GlobalTheory_CompanionTheory_KerAdj_pairing_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerAdj
namespace GlobalTheory.CompanionTheory.KerAdj
theorem _root_.solution (hK : KerBasic) (hR : RowInt) (hS : SchurInt) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (g f : Lp ℂ 2 X.ν) :
    Integrable (fun x => conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x) X.ν ∧
    Integrable (fun y => conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν) X.ν ∧
    ∫ x, conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x ∂X.ν
      = ∫ y, conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν ∂X.ν := by
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  obtain ⟨-, hc, -, -, hadj, -⟩ := hK X φ hφ
  obtain ⟨A, hA, h1, h2⟩ := hR X φ hφ
  have hg : MemLp (fun y => conj ((g : X.G → ℂ) y)) 2 X.ν := (Lp.memLp g).star
  have hI := hS X.G X.ν (ker X.Γ φ) A hc.measurable hA h1 h2 _ _ hg (Lp.memLp f)
  have := pairing_swap (ν := X.ν) (ker X.Γ φ) (g : X.G → ℂ) (f : X.G → ℂ) hI
  simpa only [hadj] using this
end GlobalTheory.CompanionTheory.KerAdj
