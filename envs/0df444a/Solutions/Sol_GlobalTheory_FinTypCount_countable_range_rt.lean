-- Prove2me | solution 1 for GlobalTheory.FinTypCount.countable_range_rt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:17.088883+00:00
-- url     : https://prove2.me/submissions/40af5ed9-e70f-45ae-aaa2-574cfd4004ea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_FinTypCount_countable_field
import Theorems.Thm_GlobalTheory_FinTypCount_exists_code
import Theorems.Thm_GlobalTheory_FinTypCount_cong_of_code
import Theorems.Thm_GlobalTheory_FinTypCount_rt_mul
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {n : ℕ}
namespace GlobalTheory.FinTypCount
theorem _root_.solution {f : GAf L n → ℂ} {N : ℕ} (hN : 0 < N)
    (hf : ∀ κ, Cong L n N κ → rt L n κ f = f) :
    (Set.range fun h : GAf L n => rt L n h f).Countable := by
  classical
  haveI := countable_field (L := L)
  choose p _ hp2 hp3 using exists_code (L := L) (n := n) N hN
  let Ψ : ℕ × (Fin n → Fin n → L) → (GAf L n → ℂ) := fun q =>
    if hq : ∃ g, p g = q then rt L n hq.choose f else 0
  have key : ∀ g, rt L n g f = Ψ (p g) := by
    intro g
    have hq : ∃ g', p g' = p g := ⟨g, rfl⟩
    simp only [Ψ, dif_pos hq]
    have e := hq.choose_spec
    have h3 := hp3 hq.choose
    rw [e] at h3
    have hc : Cong L n N (g⁻¹ * hq.choose) := cong_of_code (hp2 g) (hp3 g) h3
    calc rt L n g f = rt L n g (rt L n (g⁻¹ * hq.choose) f) := by rw [hf _ hc]
      _ = rt L n hq.choose f := by rw [← rt_mul, mul_inv_cancel_left]
  refine (Set.countable_range Ψ).mono ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨p g, (key g).symm⟩
end GlobalTheory.FinTypCount
