-- Prove2me | solution 1 for GlobalTheory.posDef_of_tendsto_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:33.485083+00:00
-- url     : https://prove2.me/submissions/25aa632b-528c-4ce1-9d20-2b508f1150e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_posDef_of_tendsto_intCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (φ : X →+ V) (hφ : Submodule.span ℝ (Set.range φ) = ⊤)
    (Q : QuadraticForm ℝ V) (h : Tendsto (fun x => Q (φ x)) cofinite atTop) : Q.PosDef := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℝ (φ : X → V)
  have : Finite κ := hli.finite
  have := Fintype.ofFinite κ
  let b : Basis κ ℝ V := Basis.mk hli (by rw [hspan, hφ])
  have hb : ∀ n : κ → ℤ, φ (∑ i, n i • a i) = b.equivFun.symm fun i => (n i : ℝ) := fun n => by
    simp [b, Int.cast_smul_eq_zsmul]
  have hinj : Function.Injective fun n : κ → ℤ => ∑ i, n i • a i := fun n m e => by
    have e' := congrArg φ e
    simp only [hb] at e'
    ext i
    exact_mod_cast congrFun (b.equivFun.symm.injective e') i
  have hp := posDef_of_tendsto_intCast (Q.comp b.equivFun.symm.toLinearMap)
    ((h.comp hinj.tendsto_cofinite).congr fun n => by simp [hb])
  intro v hv
  simpa using hp (b.equivFun v) (by simpa using hv)
end GlobalTheory
