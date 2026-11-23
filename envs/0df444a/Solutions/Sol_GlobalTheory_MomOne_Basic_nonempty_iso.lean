-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.nonempty_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:04.322807+00:00
-- url     : https://prove2.me/submissions/b184aaf5-2061-4f18-91b0-4e0b95807dcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
open scoped ComplexConjugate
namespace GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
namespace Mdl
variable (M : Mdl q)
end Mdl
namespace Basic
open Filter Topology
open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in
private theorem cardinal_le_seq_of_denseRange {X Y : Type} [TopologicalSpace X]
    [FrechetUrysohnSpace X] [T2Space X] (i : Y → X) (hi : DenseRange i) : #X ≤ #(ℕ → Y) := by
  have h : ∀ x : X, ∃ u : ℕ → Y, Tendsto (i ∘ u) atTop (𝓝 x) := by
    intro x
    have hx : x ∈ closure (Set.range i) := by rw [hi.closure_range]; trivial
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose u hu using hv
    refine ⟨u, ?_⟩
    have : i ∘ u = v := funext fun n => hu n
    rw [this]; exact hlim
  choose u hu using h
  refine Cardinal.mk_le_of_injective (f := u) fun x y hxy => ?_
  have := hu y
  rw [← hxy] at this
  exact tendsto_nhds_unique (hu x) this
open PowerSeries in
open scoped ComplexConjugate in
variable {q : ℕ} [Fact q.Prime] in
open Filter Topology in
open Cardinal in
private theorem cardinal_padicComplex_eq_continuum (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  have hQ : #ℚ_[q] ≤ 𝔠 := by
    calc #ℚ_[q] ≤ #(ℕ → ℚ) := cardinal_le_seq_of_denseRange _ (Padic.denseRange_ratCast q)
      _ = 𝔠 := by rw [← power_def, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat, aleph0_power_aleph0]
  have hA : #(PadicAlgCl q) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
      (max_le hQ aleph0_le_continuum)
  apply le_antisymm
  · calc #ℂ_[q] ≤ #(ℕ → PadicAlgCl q) :=
          cardinal_le_seq_of_denseRange _ UniformSpace.Completion.denseRange_coe
      _ = #(PadicAlgCl q) ^ ℵ₀ := by rw [← power_def, Cardinal.mk_nat]
      _ ≤ 𝔠 ^ ℵ₀ := power_le_power_right hA
      _ = 𝔠 := continuum_power_aleph0
  · obtain ⟨f, -, -, hf⟩ := Perfect.exists_nat_bool_injection
      (PerfectSpace.univ_perfect (α := ℚ_[q])) ⟨0, trivial⟩
    calc 𝔠 = #(ℕ → Bool) := by rw [← power_def, mk_bool, Cardinal.mk_nat, two_power_aleph0]
      _ ≤ #ℚ_[q] := mk_le_of_injective hf
      _ ≤ #ℂ_[q] := mk_le_of_injective (algebraMap ℚ_[q] ℂ_[q]).injective
example : Split 7 2 := Or.inl ⟨rfl, rfl⟩
example : Split 7 11 := Or.inr ⟨by norm_num, by norm_num⟩
example : ¬ Split 7 3 := by norm_num [Split]
end Basic
end GlobalTheory.MomOne
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
open PowerSeries
open scoped ComplexConjugate
variable {q : ℕ} [Fact q.Prime]
open Filter Topology
open Cardinal
namespace GlobalTheory.MomOne.Basic
namespace _root_.GlobalTheory.MomOne.Basic
theorem _root_.solution (q : ℕ) [Fact q.Prime] :
    Nonempty (ℂ ≃+* ℂ_[q]) := by
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_
  · rw [Cardinal.mk_complex]; exact aleph0_lt_continuum
  · exact Cardinal.eq.1 (by rw [Cardinal.mk_complex, cardinal_padicComplex_eq_continuum])
end _root_.GlobalTheory.MomOne.Basic
end GlobalTheory.MomOne.Basic
