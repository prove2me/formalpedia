-- Prove2me | solution 1 for GlobalTheory.SplitDict.pf_pf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:47.97399+00:00
-- url     : https://prove2.me/submissions/90fb2012-7767-41cd-a7c8-d191f094d7c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitDict_slice_mem_SB
import Theorems.Thm_GlobalTheory_SplitDict_inversion_const
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
omit [T2Space T]
namespace GlobalTheory.SplitDict
theorem _root_.solution (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (z : T × (n → k)) :
    pf ψ (Measure.pi fun _ => m) (pf ψ (Measure.pi fun _ => m) f) z =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f (z.1, -z.2) := by
  haveI := secondCountable k
  obtain ⟨t, y⟩ := z
  have hsl := slice_mem_SB hf t
  have hg : (fun w => f (t, w - y)) ∈ SB (n → k) :=
    ⟨hsl.1.comp_continuous (continuous_sub_right y), hsl.2.comp_homeomorph (Homeomorph.subRight y)⟩
  have hinv := inversion_const m h hg
  simp only [zero_sub] at hinv
  show ∫ x, (∫ w, f (t, w) * (ψ (w ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => m)) * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => m) = _ * f (t, -y)
  rw [← hinv]
  congr 1
  funext x
  rw [← integral_mul_const]
  have e := integral_sub_right_eq_self (μ := Measure.pi fun _ : n => m)
    (fun u => f (t, u) * (ψ ((u + y) ⬝ᵥ x) : ℂ)) y
  simp only [sub_add_cancel] at e
  rw [e]
  congr 1
  funext u
  rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm y x]
  ring
end GlobalTheory.SplitDict
