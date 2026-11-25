-- Prove2me | solution 1 for GlobalTheory.StepData.mul_mem_of_hat_cosetInd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:24.692427+00:00
-- url     : https://prove2.me/submissions/13b4d963-861a-4b29-a63f-ca99c0b49626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MulMemOfHatCosetIndNeZero
import Theorems.Thm_GlobalTheory_RootEx_Unram_mem_of_psi
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_StepData_IntM_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
namespace GlobalTheory.StepData
open MeasureTheory ValuativeRel Matrix in
private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField' (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨a, ha0, ha1⟩ := Valuation.RankOne.nontrivial (valuation k)
  obtain ⟨b, hb0, hb1⟩ : ∃ b : k, valuation k b ≠ 0 ∧ valuation k b < 1 := by
    rcases lt_or_gt_of_ne ha1 with h | h
    · exact ⟨a, ha0, h⟩
    · refine ⟨a⁻¹, by simpa using ha0, ?_⟩
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
  have hb : b ≠ 0 := by
    intro h
    simp [h] at hb0
  refine ⟨⟨fun m : ℕ => (fun x => (b ^ m)⁻¹ * x) '' (𝒪[k] : Set k),
    fun m => (_root_.GlobalTheory.SplitWeil.isCompact_int k).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  set S := (IsRankLeOne.nonempty (R := k)).some
  have hf := S.strictMono
  obtain ⟨m, hm⟩ : ∃ m : ℕ, S.emb (valuation k b) ^ m * S.emb (valuation k x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    have hpos : 0 < S.emb (valuation k x) := by
      rw [← map_zero S.emb]
      exact hf (zero_lt_iff.2 (by simpa using hx))
    have hlt : S.emb (valuation k b) < 1 := by
      rw [← map_one S.emb]
      exact hf hb1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hlt
    refine ⟨m, ?_⟩
    calc _ ≤ (S.emb (valuation k x))⁻¹ * S.emb (valuation k x) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨m, b ^ m * x, ?_, by field_simp⟩
  rw [SetLike.mem_coe, Valuation.mem_integer_iff, ← hf.le_iff_le, map_one, map_mul, map_mul,
    map_pow, map_pow]
  exact hm
end GlobalTheory.StepData
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.StepData
open MeasureTheory ValuativeRel Matrix
namespace GlobalTheory.StepData
namespace _root_.GlobalTheory.StepData
theorem _root_.solution : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ψ : AddChar k Circle) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : kˣ) (ε : k)
    (yb : (n → k) ⧸ _root_.GlobalTheory.StepData.box n c) (η : n → k),
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb) η ≠ 0 →
    ∀ i, ε * η i * (c : k) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ hψ ν _ n _ _ c ε yb η hne i
  haveI := sigmaCompactSpace_of_isNonarchimedeanLocalField' k
  by_contra hx
  obtain ⟨t, ht, hψt⟩ : ∃ t ∈ 𝒪[k], ψ (t * (ε * η i * c)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hx (_root_.GlobalTheory.RootEx.Unram.mem_of_psi hψ h)
  have hvmem : Pi.single i ((c : k) * t) ∈ _root_.GlobalTheory.StepData.box n c := by
    show ∀ j, valuation k (Pi.single (M := fun _ => k) i ((c : k) * t) j) ≤ valuation k (c : k)
    intro j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Pi.single_eq_same, map_mul]
      exact mul_le_of_le_one_right' ht
    · simp [Pi.single_eq_of_ne hj]
  apply hne
  unfold _root_.GlobalTheory.StepData.hat
  set g : (n → k) → ℂ := fun y => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y *
    (ψ (ε * η ⬝ᵥ y) : ℂ) with hg
  have hshift : ∀ y, g (y + Pi.single i ((c : k) * t)) = (ψ (t * (ε * η i * c)) : ℂ) * g y := by
    intro y
    have hind : _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb
        (y + Pi.single i ((c : k) * t)) =
          _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y := by
      unfold _root_.GlobalTheory.StepData.cosetInd
      simp only [Set.indicator]
      have hq : Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n c)
          (y + Pi.single i ((c : k) * t)) = Submodule.Quotient.mk y := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hvmem, add_zero]
      have hv0 := (Submodule.Quotient.mk_eq_zero _).2 hvmem
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (hq.symm.trans h₁) h₂
      · exact absurd (hq.trans h₂) h₁
      · rfl
    simp only [hg, hind, dotProduct_add, dotProduct_single, mul_add, AddChar.map_add_eq_mul,
      Circle.coe_mul]
    have hr : ε * (η i * ((c : k) * t)) = t * (ε * η i * c) := by ring
    rw [hr]
    ring
  have h1 := integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) g
    (Pi.single i ((c : k) * t))
  simp only [hshift, integral_const_mul] at h1
  have hne1 : (ψ (t * (ε * η i * c)) : ℂ) ≠ 1 := by
    intro h
    exact hψt (Circle.ext_iff.mpr (by simpa using h))
  have hzero : ((ψ (t * (ε * η i * c)) : ℂ) - 1) * (∫ y, g y ∂Measure.pi fun _ => ν) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left (sub_ne_zero.2 hne1)
end _root_.GlobalTheory.StepData
end GlobalTheory.StepData
