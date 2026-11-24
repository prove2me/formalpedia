-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:56.655319+00:00
-- url     : https://prove2.me/submissions/e362a2da-b04c-47a2-ad8a-9e24ef5920cb

import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DualLattice_exists_trace_dual
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DualLattice_eq_of_trace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.DualLattice
namespace GlobalTheory.CompanionTheory.SW.ThW.DualLattice
theorem _root_.solution (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ)
    (hB : B.det ≠ 0) (hN : 0 < N) :
    ∃ e : (ι × InfinitePlace F → ℤ) → ι → F,
      (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧
      ∀ y : ι → F, (∀ i v, ∃ m : ℤ,
        (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by
  classical
  obtain ⟨d, hd⟩ := exists_trace_dual b
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBB : ∀ c : ι → F, B *ᵥ (B⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have hinj : ∀ y : ι → F, B⁻¹ *ᵥ (B *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec]
  obtain ⟨c, hc⟩ : ∃ c : (ι × InfinitePlace F → ℤ) → ι → F,
      ∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c n i) = n (i, v) := by
    refine ⟨fun n i => ∑ u, algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u, fun n i v => ?_⟩
    have : Algebra.trace ℚ F ((b v : F) * ∑ u, algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u)
        = (n (i, v) : ℚ) / N := by
      simp only [Finset.mul_sum, map_sum]
      have hterm : ∀ u, Algebra.trace ℚ F ((b v : F) * (algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u))
          = ((n (i, u) : ℚ) / N) * (if v = u then 1 else 0) := by
        intro u
        rw [mul_left_comm, ← Algebra.smul_def, map_smul, hd, smul_eq_mul]
      rw [Finset.sum_congr rfl fun u _ => hterm u]
      simp
    simp only [this]
    field_simp
  refine ⟨fun n => B⁻¹ *ᵥ c n, fun n i v => ?_, fun y hy => ?_⟩
  · simp only [hBB]
    exact hc n i v
  · choose m hm using hy
    refine ⟨fun p => m p.1 p.2, ?_⟩
    have hcy : c (fun p => m p.1 p.2) = B *ᵥ y := by
      funext i
      exact eq_of_trace_eq b fun v =>
        mul_left_cancel₀ hNq ((hc (fun p => m p.1 p.2) i v).trans (hm i v).symm)
    change B⁻¹ *ᵥ c (fun p => m p.1 p.2) = y
    rw [hcy, hinj]
end GlobalTheory.CompanionTheory.SW.ThW.DualLattice
