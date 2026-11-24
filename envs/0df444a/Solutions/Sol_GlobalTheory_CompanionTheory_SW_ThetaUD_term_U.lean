-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.term_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:54.729857+00:00
-- url     : https://prove2.me/submissions/065427e8-e7c6-48d4-9995-f9969ac6b27f

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_form_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_form_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_trace_eq_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_gauss_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.ThetaUD
theorem _root_.solution (ψ : AddChar (A F) ℂ) (hψ : IsStdChar F ψ) (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (hQ : QSetup M B ρ P)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (hO : IsOrth B ρ gf gi)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (b : F) (x : ι → F) :
    thTerm B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) x =
      thTerm B ρ P gf gi φ τ x := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  obtain ⟨hOf, hOi⟩ := hO
  set t : F := x ⬝ᵥ (B *ᵥ x) with ht
  have hfin : qf (hf F) (Bf B) (gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      algebraMap F (A F) (1 / 2 * t) := by
    unfold qf
    rw [form_mulVec gf (Bf B) hOf]
    have := form_map (algebraMap F (A F)) B x
    unfold Bf hf
    rw [this, map_mul]
  have hinf : ∀ w, (gi w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (B.map (ρ w) *ᵥ (gi w *ᵥ fun j => ρ w (x j))) =
      ρ w t := by
    intro w
    rw [form_mulVec (gi w) _ (hOi w), form_map]
  have hphase : ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) = 1 := by
    rw [← map_mul, hψ.2, trace_eq_sum hT ρ hρ, ← Complex.exp_add]
    have : ∑ w, ((ρ w (b * (1 / 2 * t)) : ℝ) : ℂ) = (1 / 2) * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [map_mul, map_div₀, map_one, map_ofNat]
      push_cast
      ring
    rw [this]
    have h0 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) +
        (Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) = 0 := by ring
    rw [h0, Complex.exp_zero]
  unfold thTerm opU
  rw [gauss_add B ρ P τ (fun w => ρ w b), hfin]
  simp only [hinf]
  calc _ = (ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)))) *
        (φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) *
          gauss B ρ P τ fun w => gi w *ᵥ fun j => ρ w (x j)) := by ring
    _ = _ := by rw [hphase, one_mul]
end GlobalTheory.CompanionTheory.SW.ThetaUD
