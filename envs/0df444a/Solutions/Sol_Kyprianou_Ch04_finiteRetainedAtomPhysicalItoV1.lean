-- Prove2me | solution 1 for Kyprianou.Ch04.finiteRetainedAtomPhysicalItoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:32:03.501676+00:00
-- url     : https://prove2.me/submissions/ec1ccf44-05eb-4bf2-a511-0c3618d58026

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomAffinePathsV1
import Theorems.Thm_Kyprianou_Ch04_finiteAffineStepStrictLeftLimitV1
import Theorems.Thm_Kyprianou_Ch04_finiteAffineStepActualJumpV1
import Theorems.Thm_Kyprianou_Ch04_finiteAffineJumpOrdinaryPartialsChainRuleV1
import Theorems.Thm_Kyprianou_Ch04_finiteAffineLeftRightTimeIntegralV1
import Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomJumpLedgerV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Deterministic physical Ito identity on a finite retained-atom window. -/
theorem solution (R : Measure (ℝ × ℝ)) (ν : Measure ℝ)
    (T : NNReal) (e b : ℝ) (he : e < 1)
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (Y L : NNReal → ℝ)
    (hY : ∀ u ≤ T, Y u =
      b * (u : ℝ) + (∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂ R) +
      (∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂ R) -
      (u : ℝ) * (∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν))
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u)))
    (f ft fx : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (ft s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fx s x) x)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hft : ContinuousOn (fun z : ℝ × ℝ => ft z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hfx : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    f T (Y T) = f 0 0 + (∫ s in Icc (0 : ℝ) (T : ℝ), ft s (Y s.toNNReal)) +
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|},
        (f z.1 (L z.1.toNNReal + z.2) - f z.1 (L z.1.toNNReal) -
          z.2 * fx z.1 (L z.1.toNNReal)) ∂ R) +
      (b * (∫ s in Icc (0 : ℝ) (T : ℝ), fx s (L s.toNNReal)) +
        ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * fx z.1 (L z.1.toNNReal) ∂ R) +
      ((∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
          z.2 * fx z.1 (L z.1.toNNReal) ∂ R) -
        ∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in {x : ℝ | e < |x| ∧ |x| < 1},
          x * fx s (L s.toNNReal) ∂ν ∂volume) := by
  let c := ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
  let d := b - c
  let U := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) ≤ u then j r else 0
  let V := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) < u then j r else 0
  have hy (u : NNReal) (hu : u ≤ T) : Y u =
      d * (u : ℝ) + ∑ r ∈ S, if r ≤ u then j r else 0 := by
    rw [hY u hu]
    exact (Kyprianou.Ch04.physicalCommonRetainedAtomAffinePathsV1
      R T e b c he S j hS hR u hu).2
  have hl := Kyprianou.Ch04.finiteAffineStepStrictLeftLimitV1 S j d T Y L hy hL
  have hy' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) : Y s.toNNReal = U s := by
    have hst : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs.2
    rw [hy _ hst]
    simp [U,← NNReal.coe_le_coe,Real.coe_toNNReal _ hs.1]
  have hl' (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (T : ℝ)) : L s.toNNReal = V s := by
    have hst : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs.2
    rw [hl _ (Real.toNNReal_pos.mpr hs.1) hst]
    simp [V,← NNReal.coe_lt_coe,Real.coe_toNNReal _ hs.1.le]
  have hJ (r : NNReal) (hr : r ∈ S) : Y r = L r + j r := by
    have h := Kyprianou.Ch04.finiteAffineStepActualJumpV1 S j d T Y L hy hL
      r (hS r hr).1 (hS r hr).2.1
    simp only [if_pos hr] at h
    linarith
  have h := Kyprianou.Ch04.finiteAffineJumpOrdinaryPartialsChainRuleV1 S j d T
    (fun r hr => (hS r hr).1) (fun r hr => (hS r hr).2.1) f ft fx ht hx hf hft hfx
  change f T (U T) = f 0 0 + (∫ s in Icc (0 : ℝ) (T : ℝ), ft s (U s)) +
    d * (∫ s in Icc (0 : ℝ) (T : ℝ), fx s (U s)) +
    ∑ r ∈ S, (f r (U r) - f r (V r)) at h
  rw [Kyprianou.Ch04.finiteAffineLeftRightTimeIntegralV1 S j d fx T] at h
  have hft' : (∫ s in Icc (0 : ℝ) (T : ℝ), ft s (U s)) =
      ∫ s in Icc (0 : ℝ) (T : ℝ), ft s (Y s.toNNReal) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    change ft s (U s) = ft s (Y s.toNNReal)
    rw [hy' s hs]
  have hfx' : (∫ s in Icc (0 : ℝ) (T : ℝ), fx s (V s)) =
      ∫ s in Icc (0 : ℝ) (T : ℝ), fx s (L s.toNNReal) := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change fx s (V s) = fx s (L s.toNNReal)
    rw [hl' s hs]
  have hj : (∑ r ∈ S, (f r (U r) - f r (V r))) =
      ∑ r ∈ S, (f r (Y r) - f r (L r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hh := hS r hr
    rw [← hy' (r : ℝ) ⟨r.coe_nonneg,by exact_mod_cast hh.2.1⟩,
      ← hl' (r : ℝ) ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2.1⟩]
    simp
  have hT := hy' (T : ℝ) ⟨T.coe_nonneg,le_rfl⟩
  rw [Real.toNNReal_coe] at hT
  rw [← hT,hft',hfx',hj,
    Kyprianou.Ch04.physicalCommonRetainedAtomJumpLedgerV1 R T e he S j hS hR Y L f fx hJ] at h
  have hc : (∫ s in Icc (0 : ℝ) (T : ℝ),
      ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x * fx s (L s.toNNReal) ∂ν ∂volume) =
      c * (∫ s in Icc (0 : ℝ) (T : ℝ), fx s (L s.toNNReal)) := by
    simp_rw [integral_mul_const]
    exact integral_const_mul _ _
  rw [hc]
  dsimp [d] at h
  linarith
