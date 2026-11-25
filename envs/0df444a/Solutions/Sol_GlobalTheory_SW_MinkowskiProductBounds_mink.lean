-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.mink
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:51.884203+00:00
-- url     : https://prove2.me/submissions/c8d20765-4814-4baf-9b95-275e31bc4fab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_exists_basis_norm_eq_succMin
import Theorems.Thm_GlobalTheory_spanCovol_bot
import Theorems.Thm_GlobalTheory_succMin_mul_minNorm_pow_le
import Theorems.Thm_GlobalTheory_succMin_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution {W V ι : Type} [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] (b : Basis ι ℝ W) (e : W ≃ₗ[ℝ] V)
    (Δ ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, ∀ T : W →ₗ[ℝ] W, LinearMap.det T ≠ 0 →
      |LinearMap.det T| ≤ Δ → (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → ε ≤ ‖e (T x)‖) →
      ∃ v : Basis (Fin (finrank ℝ V)) ℝ W, ∀ i, v i ∈ span ℤ (Set.range b) ∧ ‖e (T (v i))‖ ≤ C := by
  classical
  borelize V
  have : FiniteDimensional ℝ W := Module.Finite.of_basis b
  let b0 := b.map e
  let c0 := MeasureTheory.volume.real (ZSpan.fundamentalDomain b0)
  have hc0 : 0 ≤ c0 := MeasureTheory.measureReal_nonneg
  refine ⟨(finrank ℝ V : ℝ) ^ ((finrank ℝ V : ℝ) / 2) * (Δ * c0) / ε ^ (finrank ℝ V - 1),
    fun T h0 hΔ hmin => ?_⟩
  let T' : W ≃ₗ[ℝ] W := LinearMap.equivOfDetNeZero T h0
  have hT' : ∀ x, T' x = T x := fun x => rfl
  let f := T'.trans e
  let b1 := b.map f
  let L := span ℤ (Set.range b1)
  have hL : ∀ y, y ∈ L ↔ f.symm y ∈ span ℤ (Set.range b) := by
    intro y
    rw [Basis.mem_span_iff_repr_mem, Basis.mem_span_iff_repr_mem]
    simp [b1]
  have hcov : ZLattice.covolume L = |LinearMap.det T| * c0 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b1 MeasureTheory.volume),
      ZSpan.measureReal_fundamentalDomain b1 MeasureTheory.volume b0]
    congr 2
    have : (b1 : ι → V) = e ∘ (T ∘ b) := by
      ext i; simp [b1, f, hT']
    rw [this, Basis.det_map]
    have h3 : (e.symm : V → W) ∘ e ∘ T ∘ b = T ∘ b := by ext i; simp
    rw [h3, Basis.det_comp, Basis.det_self, mul_one]
  obtain ⟨v, hv, hN⟩ := exists_basis_norm_eq_succMin L
  refine ⟨v.map f.symm, fun i => ⟨(hL _).1 (hv i), ?_⟩⟩
  have h1 : e (T (v.map f.symm i)) = v i := f.apply_symm_apply (v i)
  rw [h1, hN, le_div_iff₀ (by positivity)]
  have hne : L ≠ ⊥ := fun h => v.ne_zero i (by simpa [h] using hv i)
  have hm : ε ≤ minNorm L := le_minNorm hne fun y hy hy0 => by
    have := hmin _ ((hL y).1 hy) (by simpa using hy0)
    rwa [show e (T (f.symm y)) = y from f.apply_symm_apply y] at this
  have h2 := succMin_mul_minNorm_pow_le L (k := i + 1) (by omega) i.2
  refine le_trans ?_ (h2.trans ?_)
  · have := succMin_nonneg L (i + 1)
    gcongr
  · rw [hcov]; gcongr
end GlobalTheory.SW.MinkowskiProductBounds
