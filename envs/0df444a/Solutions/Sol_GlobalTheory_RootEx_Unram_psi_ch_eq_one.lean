-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.psi_ch_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:14.881784+00:00
-- url     : https://prove2.me/submissions/4a7f1d25-cefc-4576-82d4-f4cec2424781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.RootEx.Unram
namespace _root_.GlobalTheory.RootEx.Unram
theorem _root_.solution {p : ℕ} (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure]
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (h : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ ≠ 0)
    (D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hD : ∀ r s, ¬ _root_.GlobalTheory.RootEx.Free p (r, s) → D r s = 0)
    (hΨ : ∀ x, Ψ (x + D) = Ψ x) : ψ (-_root_.GlobalTheory.RootEx.ch D) = 1 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  set d : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k :=
    fun rs => D rs.1.1 rs.1.2 with hd
  have haff : ∀ e, _root_.GlobalTheory.RootEx.affPt p x₀ (e + d) = _root_.GlobalTheory.RootEx.affPt p x₀ e + D := by
    intro e
    ext r s
    simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply]
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · simp only [dif_pos hf, Pi.add_apply, hd]
      ring
    · simp only [dif_neg hf, hD r s hf, add_zero]
  have hch : ∀ A B : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
      _root_.GlobalTheory.RootEx.ch (A + B) =
        _root_.GlobalTheory.RootEx.ch A + _root_.GlobalTheory.RootEx.ch B := by
    intro A B
    simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib]
  have key : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ =
      ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ := by
    unfold _root_.GlobalTheory.RootEx.opE
    rw [← integral_const_mul, ← integral_add_right_eq_self _ d]
    congr 1
    ext e
    rw [haff, hΨ, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have h1 : ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) = 1 :=
    mul_right_cancel₀ h (key.symm.trans (one_mul _).symm)
  exact Circle.ext (h1.trans Circle.coe_one.symm)
end _root_.GlobalTheory.RootEx.Unram
end GlobalTheory.RootEx.Unram
