-- Prove2me | solution 1 for GlobalTheory.MajorantContinuity.continuousAt_maj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:51.587056+00:00
-- url     : https://prove2.me/submissions/fbeb1ce5-0bab-4914-ae61-b65bfced7cab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_cont_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
open GlobalTheory GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantContinuity
theorem _root_.solution {r : ℕ} (X : Data E r) (τ : X.Ψ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → ℂ) :
    ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, v) := by
  have hH : ∀ f g : Frame X.Ψ r × (Fin r → ℂ) → (Fin r → ℂ), Continuous f → Continuous g →
      Continuous fun p => hermC τ.1 X.Gm (f p) (g p) := by
    intro f g hf hg
    unfold hermC
    have hf' : ∀ a, Continuous fun p => f p a := fun a => (continuous_apply a).comp hf
    have hg' : ∀ b, Continuous fun p => g p b := fun b => (continuous_apply b).comp hg
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hf' a).mul continuous_const).mul (Complex.continuous_conj.comp (hg' b))
  have hcol : ∀ k : Fin r, Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => col (mat p.1 τ) k := by
    intro k
    change Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => fun i => p.1 τ i k
    exact continuous_pi fun i => (continuous_apply k).comp ((continuous_apply i).comp
      ((continuous_apply τ).comp continuous_fst))
  have hG : Continuous fun y : Frame X.Ψ r => X.gramPos y τ := by
    unfold Data.gramPos
    exact (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_gram X τ).matrix_submatrix _ _
  have hdet : (X.gramPos x τ).det ≠ 0 := (X.gramPos_posDef hx τ).det_pos.ne'
  have hI : ContinuousAt (fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) x := by
    refine (continuousAt_matrix_inv _ ?_).comp hG.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hIab : ∀ a b : Fin X.p0,
      ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹ a b) (x, v) :=
    fun a b => by
      have hI' : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹) (x, v) :=
        ContinuousAt.comp (g := fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) (f := Prod.fst) hI
          continuous_fst.continuousAt
      exact ContinuousAt.comp (g := fun M : Matrix (Fin X.p0) (Fin X.p0) ℂ => M a b)
        (continuous_id.matrix_elem a b).continuousAt hI'
  unfold Data.maj Data.posPart
  refine ContinuousAt.sub (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_))
    (Complex.continuous_re.comp (hH _ _ continuous_snd continuous_snd)).continuousAt
  refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
  exact (((hH _ _ continuous_snd (hcol _)).continuousAt.mul (hIab a b)).mul
    (Complex.continuous_conj.comp (hH _ _ continuous_snd (hcol _))).continuousAt)
end GlobalTheory.MajorantContinuity
