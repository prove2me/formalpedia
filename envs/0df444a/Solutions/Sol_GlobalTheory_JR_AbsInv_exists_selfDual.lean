-- Prove2me | solution 1 for GlobalTheory.JR.AbsInv.exists_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:59.735375+00:00
-- url     : https://prove2.me/submissions/6cd80369-e113-4487-87c9-1aa70b4fdbd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Theorems.Thm_GlobalTheory_JR_AbsInv_exists_nhds_invariant
import Theorems.Thm_GlobalTheory_JR_AbsInv_fourB_fourB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.JR MeasureTheory Filter Topology
namespace GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in
private theorem measureReal_mul_eq_of_dual_pairs_subset (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : V → V → ℂ) (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N M' N' : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hMc : IsCompact (M : Set V)) (hNo : IsOpen (N : Set V))
    (hNc : IsCompact (N : Set V)) (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1)
    (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1) (hM'o : IsOpen (M' : Set V))
    (hN'o : IsOpen (N' : Set V)) (hN'c : IsCompact (N' : Set V))
    (hN' : ∀ y, y ∈ N' ↔ ∀ x ∈ M', B x y = 1) (hM' : ∀ x, x ∈ M' ↔ ∀ y ∈ N', B x y = 1)
    (hle : (M' : Set V) ⊆ M) :
    μ.real M' * μ.real N' = μ.real M * μ.real N := by
  have hMclo : IsClopen (M : Set V) := ⟨M.isClosed_of_isOpen hMo, hMo⟩
  have hf : Continuous ((M : Set V).indicator (fun _ => (1 : ℂ))) :=
    hMclo.continuous_indicator continuous_const
  have hfc : HasCompactSupport ((M : Set V).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)
  have hinv : ∀ L : AddSubgroup V, (L : Set V) ⊆ M → ∀ x, ∀ m ∈ L,
      (M : Set V).indicator (fun _ => (1 : ℂ)) (x + m) = (M : Set V).indicator (fun _ => (1 : ℂ)) x := by
    intro L hL x m hm
    have hmM : m ∈ M := hL hm
    by_cases hx : x ∈ (M : Set V)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (M.add_mem hx hmM)]
    · have hxm : x + m ∉ (M : Set V) := fun h => hx (by simpa using M.sub_mem h hmM)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxm]
  have h1 := _root_.GlobalTheory.JR.AbsInv.fourB_fourB μ B hB hs ha M N hMo hNo hNc hN hM
    _ hf hfc (hinv M subset_rfl) 0
  have h2 := _root_.GlobalTheory.JR.AbsInv.fourB_fourB μ B hB hs ha M' N' hM'o hN'o hN'c
    hN' hM' _ hf hfc (hinv M' hle) 0
  have h0 : (M : Set V).indicator (fun _ => (1 : ℂ)) (-0) = 1 := by
    rw [neg_zero, Set.indicator_of_mem (M.zero_mem)]
  rw [h0, mul_one] at h1 h2
  exact_mod_cast h2.symm.trans h1
end GlobalTheory.JR.AbsInv
end

set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
namespace GlobalTheory.JR.AbsInv
namespace _root_.GlobalTheory.JR.AbsInv
theorem _root_.solution (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y)
    (H : ∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧
      IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) ∧
      (∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)) : ∃ μ : Measure V, _root_.GlobalTheory.JR.SelfDual μ B := by
  obtain ⟨M₀, N₀, -, hM₀o, hM₀c, hN₀o, hN₀c, hN₀, hM₀⟩ := H Set.univ univ_mem
  obtain ⟨ν, hν⟩ : ∃ ν : Measure V, ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hpos : 0 < ν.real M₀ * ν.real N₀ := by
    apply mul_pos
    · exact ENNReal.toReal_pos (hM₀o.measure_pos ν ⟨0, M₀.zero_mem⟩).ne' hM₀c.measure_lt_top.ne
    · exact ENNReal.toReal_pos (hN₀o.measure_pos ν ⟨0, N₀.zero_mem⟩).ne' hN₀c.measure_lt_top.ne
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (ν.real M₀ * ν.real N₀) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ Real.sqrt_pos.2 hpos
  have hrr : r * r = ν.real M₀ * ν.real N₀ := by
    rw [hr]
    exact Real.mul_self_sqrt hpos.le
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, c = ENNReal.ofReal r⁻¹ := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hr0
  have hct : c ≠ ⊤ := hc ▸ ENNReal.ofReal_ne_top
  haveI : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul ν hc0 hct
  have hreal : ∀ A : Set V, (c • ν).real A = r⁻¹ * ν.real A := by
    intro A
    rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, hc,
      ENNReal.toReal_ofReal (inv_nonneg.2 hr0.le), measureReal_def]
  have hone : (c • ν).real M₀ * (c • ν).real N₀ = 1 := by
    rw [hreal, hreal]
    calc r⁻¹ * ν.real M₀ * (r⁻¹ * ν.real N₀) = (ν.real M₀ * ν.real N₀) / (r * r) := by ring
      _ = 1 := by rw [hrr, div_self hpos.ne']
  refine ⟨c • ν, ?_⟩
  unfold _root_.GlobalTheory.JR.SelfDual
  refine ⟨inferInstance, ?_⟩
  intro f hf y
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  obtain ⟨U, hU, hUinv⟩ := _root_.GlobalTheory.JR.AbsInv.exists_nhds_invariant hf
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, hM⟩ :=
    H (U ∩ M₀) (inter_mem hU (hM₀o.mem_nhds M₀.zero_mem))
  have hMN : (c • ν).real M * (c • ν).real N = 1 :=
    (measureReal_mul_eq_of_dual_pairs_subset (c • ν) B hB hs ha M₀ N₀ M N hM₀o hM₀c hN₀o hN₀c
      hN₀ hM₀ hMo hNo hNc hN hM (fun x hx => (hMU hx).2)).trans hone
  rw [_root_.GlobalTheory.JR.AbsInv.fourB_fourB (c • ν) B hB hs ha M N hMo hNo hNc hN hM
    f hf'.1.continuous hf'.2 (hUinv M (fun x hx => (hMU hx).1)) y, hMN]
  simp
end _root_.GlobalTheory.JR.AbsInv
end GlobalTheory.JR.AbsInv
