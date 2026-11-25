-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.integral_tensor_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:33.319685+00:00
-- url     : https://prove2.me/submissions/642e6ab0-cc2a-4480-a659-b29cc8616dc2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
import Theorems.Thm_GlobalTheory_CompactAvgSchwartz_integral_tensor
import Theorems.Thm_GlobalTheory_CompactAvgSchwartz_lmul_apply
import Theorems.Thm_GlobalTheory_CompactAvgSchwartz_sum_mul_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz
namespace GlobalTheory.CompactAvgSchwartz
theorem _root_.solution {S R ι : Type} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype ι] {m n : ℕ} (ν : Measure S)
    [IsFiniteMeasure ν] (A Ai : S → ι → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ τ, Continuous fun s => A s τ)
    (hAi : ∀ τ, Continuous fun s => Ai s τ) (h : ∀ s τ, Ai s τ * A s τ = 1)
    (B Bi : S → Matrix (Fin m) (Fin m) R) (hB : Continuous B) (hBi : Continuous Bi) (h' : ∀ s, Bi s * B s = 1)
    (f : SchwartzMap (ι → Fin m → Fin n → ℂ) ℂ) {g : (Fin m → Fin n → R) → ℂ} (hg : g ∈ WeilM.SB (Fin m → Fin n → R)) :
    (∀ (x : ι → Fin m → Fin n → ℂ) (y : Fin m → Fin n → R),
      Integrable (fun s => f (fun τ i j => ∑ c, A s τ i c * x τ c j) * g (fun i j => ∑ c, B s i c * y c j)) ν) ∧
    ∃ (t : Finset ((Fin m → Fin n → R) → ℂ)) (F : ((Fin m → Fin n → R) → ℂ) → SchwartzMap (ι → Fin m → Fin n → ℂ) ℂ),
      (∀ g' ∈ t, g' ∈ WeilM.SB (Fin m → Fin n → R)) ∧
      ∀ (x : ι → Fin m → Fin n → ℂ) (y : Fin m → Fin n → R),
        ∫ s, f (fun τ i j => ∑ c, A s τ i c * x τ c j) * g (fun i j => ∑ c, B s i c * y c j) ∂ν =
          ∑ g' ∈ t, F g' x * g' y := by
  have hLc : ∀ A' : S → ι → Matrix (Fin m) (Fin m) ℂ, (∀ τ, Continuous fun s => A' s τ) →
      Continuous fun s => lmul n (A' s) := by
    intro A' hA'
    refine continuous_clm_apply.2 fun X => ?_
    simp only [lmul_apply]
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      continuous_finsetSum _ fun c _ => ?_
    exact ((hA' τ).matrix_elem i c).mul continuous_const
  have haC : ∀ B' : S → Matrix (Fin m) (Fin m) R, Continuous B' →
      Continuous fun p : S × (Fin m → Fin n → R) => fun i j => ∑ c, B' p.1 i c * p.2 c j := by
    intro B' hB'
    refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun c _ => ?_
    exact ((hB'.comp continuous_fst).matrix_elem i c).mul
      ((continuous_apply j).comp ((continuous_apply c).comp continuous_snd))
  obtain ⟨h1, t, F, ht, hF⟩ := integral_tensor ν (fun s => lmul n (A s)) (fun s => lmul n (Ai s))
    (hLc A hA) (hLc Ai hAi)
    (fun s x => by
      show lmul n (Ai s) (lmul n (A s) x) = x
      simp only [lmul_apply]
      funext τ
      exact sum_mul_cancel (h s τ) (x τ))
    (fun s y i j => ∑ c, B s i c * y c j) (fun s y i j => ∑ c, Bi s i c * y c j) (haC B hB) (haC Bi hBi)
    (fun s y => sum_mul_cancel (h' s) y) f hg
  exact ⟨fun x y => by simpa only [lmul_apply] using h1 x y, t, F, ht,
    fun x y => by simpa only [lmul_apply] using hF x y⟩
end GlobalTheory.CompactAvgSchwartz
