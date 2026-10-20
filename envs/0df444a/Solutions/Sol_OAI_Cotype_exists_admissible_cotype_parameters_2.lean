-- Prove2me | solution 2 for OAI.Cotype.exists_admissible_cotype_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:39:14.883547+00:00
-- url     : https://prove2.me/submissions/c30a6e3f-d4c3-42c9-a4e4-0d7aa8dbbc04

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ParameterChoice.lean:L43-L100
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_admissible_cotype_parameters. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevBounds
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevTruncation
import Definitions.Def_OAI_Analysis_Cotype_BivariateSplit
import Definitions.Def_OAI_Analysis_Cotype_ProjectionDerivatives
import Definitions.Def_OAI_Analysis_Cotype_MixedDerivative
import Definitions.Def_OAI_Analysis_Cotype_CoefficientCompactness
import Definitions.Def_OAI_Analysis_Cotype_GrowthScalarData
import Definitions.Def_OAI_Analysis_Cotype_TaggedCoefficient
import Definitions.Def_OAI_Analysis_Cotype_RankWalsh
import Definitions.Def_OAI_Analysis_Cotype_UniformDecay
import Definitions.Def_OAI_Analysis_Cotype_CompactDomain

-- ---- from OAI.Analysis.Cotype.ParameterChoice ----
namespace OAI

noncomputable section

namespace Cotype

theorem degreeCutoff_pow_two (N : ℕ) : degreeCutoff (2^N) = 2*N := by
  unfold degreeCutoff
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  simp only [mul_one]
  exact_mod_cast Nat.ceil_natCast (2*N)

theorem twice_lt_two_pow {N : ℕ} (hN : 3 ≤ N) : 2*N < 2^N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih => rw [pow_succ]; omega

theorem eventually_cube_le_exponential {b A : ℝ} (hb : 1 < b) (hA : 0 < A) :
    ∀ᶠ N : ℕ in Filter.atTop, A*(N : ℝ)^3 ≤ b^N := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 3 hb).eventually
    (gt_mem_nhds (one_div_pos.mpr hA))
  filter_upwards [h] with N hN
  have hh := (div_lt_div_iff₀ (pow_pos (by linarith : 0 < b) N) hA).mp hN
  nlinarith

theorem source_lift_scale (x A C q : ℝ) (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) :
    x*(1/(A*(C*x^(1/2-1/q))*Real.sqrt x)) = x^(1/q)/(A*C) := by
  have he : x^(1/2-1/q)*Real.sqrt x*x^(1/q) = x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx, ← Real.rpow_add hx]
    convert Real.rpow_one x using 1
    congr 1
    ring
  have hpow := Real.rpow_pos_of_pos hx (1/2-1/q)
  have hsqrt := Real.sqrt_pos.mpr hx
  field_simp
  convert he.symm using 1
  congr 2
  ring_nf

theorem exists_admissible_cotype_parameters (q r CF CY : ℝ)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hCF : 1 ≤ CF) (hCY : 1 ≤ CY) :
    ∃ m : ℕ, 0 < m ∧
      1 ≤ CY*(m : ℝ)^(1/2-1/r) ∧ 1 ≤ CF*(m : ℝ)^(1/2-1/q) ∧
      4 ≤ degreeCutoff m ∧ degreeCutoff m < m ∧
      80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
        min ((m : ℝ)*(1/(2*24*(12*(CY*(m : ℝ)^(1/2-1/r)))*Real.sqrt m)))
          ((m : ℝ)*(1/(2*24*(CF*(m : ℝ)^(1/2-1/q))*Real.sqrt m))) := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have hCF0 : 0 < CF := by linarith
  have hCY0 : 0 < CY := by linarith
  have hbq : 1 < (2 : ℝ)^(1/q) := Real.one_lt_rpow (by norm_num) (one_div_pos.mpr hq0)
  have hbr : 1 < (2 : ℝ)^(1/r) := Real.one_lt_rpow (by norm_num) (one_div_pos.mpr hr0)
  obtain ⟨N,hN,hbigq,hbigr⟩ := Filter.Eventually.exists
    ((Filter.eventually_ge_atTop 4).and
      ((eventually_cube_le_exponential hbq (by positivity : 0 < 1440*48*CF)).and
       (eventually_cube_le_exponential hbr (by positivity : 0 < 1440*576*CY))))
  let m := 2^N
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hqe : 0 ≤ 1/2-1/q := sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hq)
  have hre : 0 ≤ 1/2-1/r := sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hr)
  have hd : degreeCutoff m = 2*N := degreeCutoff_pow_two N
  refine ⟨m,hm0,?_,?_,by rw [hd]; omega,by rw [hd]; exact twice_lt_two_pow (by omega),?_⟩
  · nlinarith [Real.one_le_rpow hm1 hre]
  · nlinarith [Real.one_le_rpow hm1 hqe]
  have hpoly : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤ 1440*(N : ℝ)^3 := by
    rw [hd]
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hs : (2*(N : ℝ)+1)^2 ≤ (3*(N : ℝ))^2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 80*(2*(N : ℝ)) by positivity)]
  have hpow (p : ℝ) : (m : ℝ)^p = ((2 : ℝ)^p)^N := by
    dsimp [m]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num)]
  have hdscale : (m : ℝ)*(1/(2*24*(12*(CY*(m : ℝ)^(1/2-1/r)))*Real.sqrt m)) =
      ((2 : ℝ)^(1/r))^N/(576*CY) := by
    rw [← hpow]
    convert source_lift_scale (m : ℝ) 576 CY r hmR (by norm_num) hCY0 using 1
    congr 2
    ring
  have hpscale : (m : ℝ)*(1/(2*24*(CF*(m : ℝ)^(1/2-1/q))*Real.sqrt m)) =
      ((2 : ℝ)^(1/q))^N/(48*CF) := by
    rw [← hpow]
    convert source_lift_scale (m : ℝ) 48 CF q hmR (by norm_num) hCF0 using 1
    congr 2
    ring
  rw [hdscale,hpscale]
  apply le_min
  · apply hpoly.trans
    apply (le_div_iff₀ (by positivity : 0 < 576*CY)).mpr
    nlinarith
  · apply hpoly.trans
    apply (le_div_iff₀ (by positivity : 0 < 48*CF)).mpr
    nlinarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.exists_admissible_cotype_parameters := @_root_.OAI.Cotype.exists_admissible_cotype_parameters
