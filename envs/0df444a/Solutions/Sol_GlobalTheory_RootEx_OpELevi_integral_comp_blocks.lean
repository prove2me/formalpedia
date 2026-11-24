-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.integral_comp_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:59.367428+00:00
-- url     : https://prove2.me/submissions/f62da7e7-1140-4d2e-90c0-1c8f16cf565d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_pow
import Theorems.Thm_GlobalTheory_SplitWeil_linear_change_of_variables


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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution {F n J : Type} [Fintype F] [Fintype n] [DecidableEq n] [Fintype J]
    (ν : Measure k) [ν.IsAddHaarMeasure] (ι : n × J → F) (hι : Function.Injective ι)
    (A : Matrix n n k) (u : kˣ) (hu : A.det = u) (T : (F → k) → (F → k))
    (h1 : ∀ e r j, T e (ι (r, j)) = ∑ s, A r s * e (ι (s, j)))
    (h2 : ∀ e f, f ∉ Set.range ι → T e f = e f) (f : (F → k) → ℂ) :
    ∫ e, f (T e) ∂(Measure.pi fun _ => ν) =
      ((nabs k u ^ Fintype.card J)⁻¹ : ℝ) • ∫ e, f e ∂(Measure.pi fun _ => ν) := by
  classical
  let σ : (n × J) ⊕ {f // f ∉ Set.range ι} ≃ F :=
    (Equiv.sumCongr (Equiv.ofInjective ι hι) (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range ι))
  have σl : ∀ x, σ (Sum.inl x) = ι x := fun x => rfl
  have σr : ∀ x, σ (Sum.inr x) = x.1 := fun x => rfl
  let G : Matrix F F k := Matrix.reindex σ σ (fromBlocks (blockDiagonal fun _ : J => A) 0 0 1)
  have hG : G.det = (u ^ Fintype.card J : kˣ) := by
    simp [G, det_blockDiagonal, hu]
  have hG0 : G.det ≠ 0 := by rw [hG]; exact Units.ne_zero _
  have hT : ∀ e, T e = G.mulVec e := by
    intro e
    funext x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [Matrix.mulVec, dotProduct, ← σ.sum_comp]
    rcases y with ⟨r, j⟩ | y
    · have : σ.symm (ι (r, j)) = Sum.inl (r, j) := by rw [← σl]; simp
      simp [G, this, σl, σr, h1, Fintype.sum_sum_type, Fintype.sum_prod_type, blockDiagonal_apply]
    · rw [σr, h2 _ _ y.2]
      have : σ.symm y.1 = Sum.inr y := by rw [← σr]; simp
      simp [G, this, Fintype.sum_sum_type, Matrix.one_apply, σr]
  have key := (GlobalTheory.SplitWeil.linear_change_of_variables k F F ν).1 (Matrix.GeneralLinearGroup.mkOfDetNeZero G hG0) f
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero G hG0)
      = u ^ Fintype.card J := by
    ext
    rw [← hG]; rfl
  rw [hd, nabs_pow] at key
  simp only [hT]
  exact key
end GlobalTheory.RootEx.OpELevi
