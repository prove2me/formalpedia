-- Prove2me | solution 1 for OAI.Cotype.exists_levelSum_moment_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:32:41.233399+00:00
-- url     : https://prove2.me/submissions/dde55cf1-d422-4ebc-9a05-84181d8b8dea

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CompactMomentAssembly.lean:L19-L92
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_levelSum_moment_lift. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem cubeL2_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    cubeL2 X (fun ε => a • f ε) = |a| * cubeL2 X f := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => a • f ε) : PiLp 2 (fun _ : Cube n => X)) =
      a • toLp 2 f := rfl
  rw [he, norm_smul, Real.norm_eq_abs]
  ring

omit [NormedSpace ℝ X] in
theorem cubeL2_const {n : ℕ} (x : X) : cubeL2 X (fun _ : Cube n => x) = ‖x‖ := by
  simp [cubeL2, average, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WeightedCompact ----
namespace OAI

noncomputable section

open scoped BigOperators Topology ENNReal
open Filter
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)

omit [CompleteSpace X] in
theorem levelTerm_norm (l : ℕ) : ‖levelTerm A l‖ ≤ (1/2 : ℝ)^l := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1/2 : ℝ)^l)] using
    mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) z l)
      (by positivity : 0 ≤ (1/2 : ℝ)^l)

omit [CompleteSpace X] in
theorem levelTerm_summable_norm : Summable (fun l => ‖levelTerm A l‖) :=
  Summable.of_nonneg_of_le (fun l => norm_nonneg (levelTerm A l)) (levelTerm_norm A)
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))

theorem levelTerm_summable : Summable (levelTerm A) := Summable.of_norm (f := levelTerm A) (levelTerm_summable_norm A)

theorem weightedMap_summable_apply (z : LevelSum A) :
    Summable (fun l => (1/2 : ℝ)^l • (z l : X)) :=
  (ContinuousLinearMap.apply ℝ X z).summable (f := levelTerm A) (levelTerm_summable A)

theorem weightedMap_apply (z : LevelSum A) :
    weightedMap A z = ∑' l, (1/2 : ℝ)^l • (z l : X) := by
  exact ((ContinuousLinearMap.apply ℝ X z).map_tsum (levelTerm_summable A))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.L2Sequence ----
namespace OAI

noncomputable section

open scoped BigOperators ENNReal
namespace Cotype
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem lp_two_summable_sq (z : lp E 2) : Summable (fun i => ‖z i‖^2) := by
  simpa using (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem lp_two_norm_sq (z : lp E 2) : ‖z‖^2 = ∑' i, ‖z i‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem mem_lp_two_of_summable_sq (z : ∀ i, E i) (hz : Summable (fun i => ‖z i‖^2)) :
    Memℓp z 2 := by
  apply memℓp_gen
  simpa using hz

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem cubeL2_lp_sq {m : ℕ} (H : Cube m → lp E 2) :
    cubeL2 (lp E 2) H ^ 2 = ∑' i, cubeL2 (E i) (fun ε => H ε i)^2 := by
  simp only [cubeL2_sq, lp_two_norm_sq, average, smul_eq_mul]
  rw [tsum_mul_left]
  congr 1
  exact (Summable.tsum_finsetSum (fun ε _ => lp_two_summable_sq (H ε))).symm

theorem norm_sq_le_card_cubeL2_sq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} (H : Cube m → X) (ε : Cube m) :
    ‖H ε‖^2 ≤ (Fintype.card (Cube m) : ℝ) * cubeL2 X H^2 := by
  rw [cubeL2_sq]
  have hc : (Fintype.card (Cube m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  exact Finset.single_le_sum (fun a _ => sq_nonneg ‖H a‖) (Finset.mem_univ ε)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CompactMomentAssembly ----
namespace OAI

noncomputable section

open scoped BigOperators ENNReal
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)

theorem moment_clm {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {m : ℕ}
    (T : Y →L[ℝ] Z) (f : Cube m → Y) (i : Fin m) :
    T (moment Y f i) = moment Z (fun ε => T (f ε)) i := by
  simp [moment, average]

theorem exists_levelSum_moment_lift {m : ℕ} {D : ℝ} (hD : 0 < D)
    (hL : ∀ l, FiniteLevelLift m D (A l) (A (l+1))) (z : Fin m → LevelSum A) :
    ∃ H : Cube m → LevelSum A,
      (∀ i, weightedMap A (moment (LevelSum A) H i) = weightedMap A (z i)) ∧
      cubeL2 (LevelSum A) H ≤ 6 * D * Real.sqrt (∑ i, ‖z i‖^2) := by
  classical
  choose L hLm hLn using (fun l => hL l (fun i => z i l))
  have hzsum : Summable (fun l => ∑ i, ‖z i l‖^2) := by
    have hs (s : Finset (Fin m)) : Summable (fun l => ∑ i ∈ s, ‖z i l‖^2) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (lp_two_summable_sq (z i)).add ih
    exact hs Finset.univ
  have hLsq (l : ℕ) : cubeL2 (A (l+1)) (L l)^2 ≤ (3*D)^2 * ∑ i, ‖z i l‖^2 := by
    have h := (sq_le_sq₀ (cubeL2_nonneg (L l)) (by positivity)).mpr (hLn l)
    simpa only [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i l‖))] using h
  have hLsum : Summable (fun l => cubeL2 (A (l+1)) (L l)^2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hLsq (hzsum.mul_left _)
  have hεsum (ε : Cube m) : Summable (fun l => ‖L l ε‖^2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _)
      (fun l => norm_sq_le_card_cubeL2_sq (L l) ε) (hLsum.mul_left _)
  let raw (ε : Cube m) : ∀ l, A l
    | 0 => 0
    | l+1 => (2 : ℝ) • L l ε
  have hraw (ε : Cube m) : Memℓp (raw ε) 2 := by
    apply mem_lp_two_of_summable_sq
    apply (summable_nat_add_iff 1).mp
    simpa [raw, norm_smul, mul_pow, show (2 : ℝ)^2 = 4 by norm_num] using (hεsum ε).mul_left 4
  let H : Cube m → LevelSum A := fun ε => ⟨raw ε, hraw ε⟩
  have hzero (i : Fin m) : (moment (LevelSum A) H i 0 : X) = 0 := by
    have he := moment_clm ((A 0).subtypeL.comp (lp.evalCLM ℝ (fun l => A l) 2 0)) H i
    change (moment (LevelSum A) H i 0 : X) = moment X (fun _ => 0) i at he
    simpa [moment, average] using he
  have hsucc (i : Fin m) (l : ℕ) :
      (moment (LevelSum A) H i (l+1) : X) = (2 : ℝ) • (z i l : X) := by
    have he := moment_clm ((A (l+1)).subtypeL.comp (lp.evalCLM ℝ (fun l => A l) 2 (l+1))) H i
    change (moment (LevelSum A) H i (l+1) : X) =
      moment X (fun ε => (2:ℝ) • (L l ε : X)) i at he
    rw [he]
    have hs : moment X (fun ε => (2:ℝ) • (L l ε : X)) i =
        (2 : ℝ) • moment X (fun ε => (L l ε : X)) i := by
      simp [moment, average, Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]
    rw [hs, hLm]
  refine ⟨H, ?_, ?_⟩
  · intro i
    rw [weightedMap_apply, (weightedMap_summable_apply A (moment (LevelSum A) H i)).tsum_eq_zero_add]
    simp only [hzero, smul_zero, zero_add, hsucc]
    rw [weightedMap_apply]
    apply tsum_congr
    intro l
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring
  · apply (sq_le_sq₀ (cubeL2_nonneg H) (by positivity)).mp
    rw [cubeL2_lp_sq]
    have he : (fun l => cubeL2 (A l) (fun ε => H ε l)^2) =
        fun l => match l with | 0 => 0 | k+1 => 4 * cubeL2 (A (k+1)) (L k)^2 := by
      funext l
      cases l with
      | zero => simp [H, raw, cubeL2_const]
      | succ l => norm_num [H, raw, cubeL2_smul, mul_pow]
    rw [he]
    have hs : Summable (fun l => match l with | 0 => (0:ℝ) | k+1 => 4 * cubeL2 (A (k+1)) (L k)^2) := by
      apply (summable_nat_add_iff 1).mp
      simpa using hLsum.mul_left 4
    rw [hs.tsum_eq_zero_add, zero_add, tsum_mul_left]
    have htotal : ∑' l, ∑ i, ‖z i l‖^2 = ∑ i, ‖z i‖^2 := by
      rw [Summable.tsum_finsetSum (fun i _ => lp_two_summable_sq (z i))]
      simp_rw [← lp_two_norm_sq]
    have hn := hLsum.tsum_le_tsum hLsq (hzsum.mul_left ((3*D)^2))
    rw [tsum_mul_left, htotal] at hn
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
    nlinarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators ENNReal


theorem solution : type_of% @_root_.OAI.Cotype.exists_levelSum_moment_lift := @_root_.OAI.Cotype.exists_levelSum_moment_lift
