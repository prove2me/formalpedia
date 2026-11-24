-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.analytic_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:06.558965+00:00
-- url     : https://prove2.me/submissions/171d612a-2b90-465e-b018-9dc6d8210c45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_comm_S
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_fact
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_pow_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution : ∀ (V H : Type) [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (j : V →ₗ[ℂ] H) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Z : ι → Module.End ℂ V) (K : Finset ι) (m : ℕ) (y : Fin m → V) (d o : Fin m → Fin m → ℂ)
    (c : ι → ι → ι → ℂ),
    (∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w))) →
    (∀ κ i, Z κ * Z i - Z i * Z κ = ∑ l, c κ i l • Z l) →
    (∀ i, (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) * Z i =
      Z i * (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ)) →
    (∀ b, (∑ κ ∈ K, Z κ * Z κ) (y b) = ∑ e, d b e • y e) →
    (∀ b, (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) (y b) = ∑ e, o b e • y e) →
    ∀ (x : ι → ℂ), ∀ v ∈ Submodule.span ℂ (Set.range y), ∃ M C : ℝ, ∀ k : ℕ,
      ‖j (((∑ i, x i • Z i) ^ k) v)‖ ≤ M * C ^ k * (k.factorial : ℝ) := by
  intro V H _ _ _ _ j ι _ _ Z K m y d o c hskew hcomm hΩ hd ho x v hv
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  have hT : ∑ i, Z i * Z i = (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) +
      ∑ κ ∈ K, Z κ * Z κ + ∑ κ ∈ K, Z κ * Z κ := by
    rw [← Finset.sum_add_sum_compl K (fun i => Z i * Z i)]
    abel
  have hS : ∀ i, (∑ κ ∈ K, Z κ * Z κ) * Z i - Z i * (∑ κ ∈ K, Z κ * Z κ) =
      ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ) :=
    GlobalTheory.CompanionTheory.AnalyticWord.comm_S Z K c hcomm
  have hB := fun k => GlobalTheory.CompanionTheory.AnalyticWord.bnd_fact j Z y (∑ κ ∈ K, Z κ * Z κ)
    (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) K c d o hskew hT hS hΩ hd ho k
  refine ⟨(∑ f, ‖a f‖) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y 0,
    (∑ i, ‖x i‖) * (√(GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) +
      2 * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c + 1), fun k => ?_⟩
  have hf : ∀ f, ‖a f • j (((∑ i, x i • Z i) ^ k) (y f))‖ ≤
      ‖a f‖ * ((∑ i, ‖x i‖) ^ k * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y k) := by
    intro f
    have h := GlobalTheory.CompanionTheory.AnalyticWord.pow_bound j Z y x k [] f
    rw [GlobalTheory.CompanionTheory.AnalyticWord.word_nil, Module.End.one_apply, List.length_nil, zero_add] at h
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  simp only [map_sum, map_smul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun f _ => hf f).trans ?_)
  rw [← Finset.sum_mul, mul_pow]
  have hsa : 0 ≤ ∑ f, ‖a f‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsx : 0 ≤ (∑ i, ‖x i‖) ^ k := pow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) k
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB k) hsx) hsa).trans (le_of_eq ?_)
  ring
end GlobalTheory.CompanionTheory.AnalyticWord
