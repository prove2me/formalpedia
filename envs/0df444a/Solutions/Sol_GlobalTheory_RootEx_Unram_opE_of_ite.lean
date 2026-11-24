-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.opE_of_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:12.793526+00:00
-- url     : https://prove2.me/submissions/5ac12d72-d58a-473b-bba5-bccc758fb863

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Theorems.Thm_GlobalTheory_RootEx_Unram_psi_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
namespace GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = e ⟨(r, s), hf⟩ := by
  simp only [_root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, Matrix.add_apply,
    Matrix.of_apply, dif_pos hf]
  have hf' := hf
  rcases r with i | l <;> rcases s with j | m <;> simp only [_root_.GlobalTheory.RootEx.Free] at hf' <;>
    simp [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    omega
variable [MeasurableSpace k] [BorelSpace k]
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem ch_affPt_mem_of_integral {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) (he : ∀ rs, e rs ∈ 𝒪[k]) :
    _root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ∈ 𝒪[k] := by
  unfold _root_.GlobalTheory.RootEx.ch
  refine sum_mem fun i _ => ?_
  have hf : _root_.GlobalTheory.RootEx.Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by
    simp [_root_.GlobalTheory.RootEx.Free]
  rw [affPt_apply_of_free x₀ e hf]
  exact he _
end GlobalTheory.RootEx.Unram
end

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
open Classical
namespace GlobalTheory.RootEx.Unram
namespace _root_.GlobalTheory.RootEx.Unram
theorem _root_.solution {p : ℕ} {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {ν : Measure k} (hν : _root_.GlobalTheory.SplitWeil.IsUnitVol ν)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (P : Prop)
    (h : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) = if P ∧ ∀ rs, e rs ∈ 𝒪[k] then 1 else 0) :
    _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ = if P then 1 else 0 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  haveI := hν.1
  set S : Set ({ rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k) :=
    Set.univ.pi fun _ => (𝒪[k] : Set k) with hS
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => (_root_.GlobalTheory.SplitWeil.isOpen_int k).measurableSet
  have hint : ∀ e : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k,
      Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) *
          ((ψ (-_root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt p x₀ e)) : Circle) : ℂ) =
        if P then S.indicator (fun _ => (1 : ℂ)) e else 0 := by
    intro e
    rw [h e]
    by_cases hP : P
    · by_cases he : ∀ rs, e rs ∈ 𝒪[k]
      · have heS : e ∈ S := fun rs _ => he rs
        rw [if_pos ⟨hP, he⟩, if_pos hP, Set.indicator_of_mem heS,
          _root_.GlobalTheory.RootEx.Unram.psi_eq_one hψ
            (neg_mem (ch_affPt_mem_of_integral x₀ e he))]
        simp
      · have heS : e ∉ S := fun heS => he fun rs => heS rs (Set.mem_univ _)
        rw [if_neg (fun h' => he h'.2), if_pos hP, Set.indicator_of_notMem heS, zero_mul]
    · rw [if_neg (fun h' => hP h'.1), if_neg hP, zero_mul]
  unfold _root_.GlobalTheory.RootEx.opE
  simp_rw [hint]
  split_ifs with hP
  · rw [integral_indicator_const _ hSm, Measure.real_def, hS, Measure.pi_pi]
    simp [hν.2]
  · simp
end _root_.GlobalTheory.RootEx.Unram
end GlobalTheory.RootEx.Unram
