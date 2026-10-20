-- Prove2me | solution 1 for OAI.Cotype.identity_walsh_decay_of_fixedCotype
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:36:40.104991+00:00
-- url     : https://prove2.me/submissions/27ffc710-632c-43b2-8df5-2a9e76fb70d3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/IdentityWalshDecay.lean:L13-L55
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.identity_walsh_decay_of_fixedCotype. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_compactMap_walsh_bound
import Theorems.Thm_OAI_Cotype_exists_compactDomain
import Theorems.Thm_OAI_Cotype_exists_uniform_walsh_decay

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

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem cubeL2_mono {n : ℕ} {f : Cube n → X} {g : Cube n → Y}
    (h : ∀ ε, ‖f ε‖ ≤ ‖g ε‖) : cubeL2 X f ≤ cubeL2 Y g := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun ε _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h ε))

omit [NormedSpace ℝ X] in
theorem cubeL2_bound {n : ℕ} {f : Cube n → X} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ ε, ‖f ε‖ ≤ M) : cubeL2 X f ≤ M := by
  have h := cubeL2_mono (g := fun _ : Cube n => M) (by simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hf)
  simpa [cubeL2_const, Real.norm_eq_abs, abs_of_nonneg hM] using h

theorem cubeL2_clm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (fun ε => T (f ε)) ≤ ‖T‖ * cubeL2 X f := by
  have hh := cubeL2_mono (g := fun ε => ‖T‖ • f ε) (fun ε => by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using T.le_opNorm (f ε))
  simpa [cubeL2_smul, abs_of_nonneg (norm_nonneg T)] using hh

theorem vectorWalsh_L2_le {n : ℕ} (f : Cube n → X) :
    cubeL2 X (vectorWalsh f) ≤ cubeL2 X f :=
  cubeL2_bound (cubeL2_nonneg f) (vectorWalsh_bound f)

theorem operatorWalsh_L2_le {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ ‖T‖ * cubeL2 X f :=
  (vectorWalsh_L2_le _).trans (cubeL2_clm T f)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshNorm ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem walshOutputs_zero (n : ℕ) (T : X →L[ℝ] Y) : 0 ∈ walshOutputs n T := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp [operatorWalsh, vectorWalsh, average, cubeL2]

theorem walshOutputs_bddAbove (n : ℕ) (T : X →L[ℝ] Y) : BddAbove (walshOutputs n T) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (operatorWalsh_L2_le T f).trans ((mul_le_mul_of_nonneg_left hf (norm_nonneg T)).trans_eq (mul_one _))

theorem walshNorm_nonneg (n : ℕ) (T : X →L[ℝ] Y) : 0 ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) (walshOutputs_zero n T)

theorem le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) {f : Cube n → X} (hf : cubeL2 X f ≤ 1) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) ⟨f, hf, rfl⟩

theorem vectorWalsh_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    vectorWalsh (fun u => a • f u) = fun v => a • vectorWalsh f v := by
  funext v
  simp only [vectorWalsh, average, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem operatorWalsh_smul {n : ℕ} (T : X →L[ℝ] Y) (a : ℝ) (f : Cube n → X) :
    operatorWalsh T (fun u => a • f u) = fun v => a • operatorWalsh T f v := by
  simp only [operatorWalsh, map_smul]
  exact vectorWalsh_smul a _

theorem operatorWalsh_le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T * cubeL2 X f := by
  by_cases hz : cubeL2 X f = 0
  · simpa [hz] using operatorWalsh_L2_le T f
  · have hp : 0 < cubeL2 X f := lt_of_le_of_ne (cubeL2_nonneg f) (Ne.symm hz)
    have hin : cubeL2 X (fun u => (cubeL2 X f)⁻¹ • f u) ≤ 1 := by
      rw [cubeL2_smul, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz]
    have hh := le_walshNorm T hin
    rw [operatorWalsh_smul, cubeL2_smul, abs_of_pos (inv_pos.mpr hp)] at hh
    calc
      _ = ((cubeL2 X f)⁻¹ * cubeL2 Y (operatorWalsh T f)) * cubeL2 X f := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hh hp.le

theorem walshNorm_le_of_bound {n : ℕ} (T : X →L[ℝ] Y) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ f : Cube n → X, cubeL2 Y (operatorWalsh T f) ≤ D * cubeL2 X f) :
    walshNorm n T ≤ D := by
  apply csSup_le ⟨0, walshOutputs_zero n T⟩
  rintro r ⟨f, hf, rfl⟩
  exact (h f).trans ((mul_le_mul_of_nonneg_left hf hD).trans_eq (mul_one D))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CompactDomainSource ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fixedCotypeBound_pos [Nontrivial X] {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound X m D) : 0 < D := by
  obtain ⟨x,hx⟩ := exists_ne (0 : X)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : 0 < Real.sqrt (∑ _ : Fin m, ‖x‖^2) := by
    apply Real.sqrt_pos.mpr
    simpa using mul_pos (show (0:ℝ) < m by exact_mod_cast hm) (sq_pos_of_pos hxpos)
  have h := hD.2 (fun _ : Fin m => x)
  by_contra hn
  have hn' : D ≤ 0 := le_of_not_gt hn
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg hn' (cubeL2_nonneg (rademacherSum X (fun _ : Fin m => x)))
  linarith

theorem dual_fixedCotypeBound_pos [Nontrivial X] {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) : 0 < D := by
  obtain ⟨x,hx⟩ := exists_ne (0 : X)
  obtain ⟨f,_,hf⟩ := exists_dual_vector'' ℝ x
  have hf0 : f ≠ 0 := by
    intro h
    have he : f x = ‖x‖ := by exact_mod_cast hf
    rw [h] at he
    have hxpos := norm_pos_iff.mpr hx
    exact hxpos.ne' (by simpa using he.symm)
  let : Nontrivial (X →L[ℝ] ℝ) := ⟨⟨f,0,hf0⟩⟩
  exact fixedCotypeBound_pos hm hD

theorem exists_compactDomain_source [CompleteSpace X] [Nontrivial X]
    {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D)
    (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    Nonempty (CompactDomainWitness E m D) :=
  exists_compactDomain hD (dual_fixedCotypeBound_pos hm hD) E

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.IdentityWalshDecay ----
namespace OAI

noncomputable section

universe u
namespace Cotype
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]

theorem identity_walsh_decay_of_fixedCotype (hAP : ApproximationProperty X)
    (m : ℕ) (Ddual Dprimal : ℝ) (hDd : 1 ≤ Ddual) (hDp : 1 ≤ Dprimal)
    (hdual : FixedCotypeBound (X →L[ℝ] ℝ) m Ddual)
    (hprimal : FixedCotypeBound X m Dprimal)
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*(12*Ddual)*Real.sqrt m)))
        ((m : ℝ)*(1/(2*24*Dprimal*Real.sqrt m)))) :
    Filter.Tendsto (fun N => walshNorm N (ContinuousLinearMap.id ℝ X)) Filter.atTop (nhds 0) := by
  have hm : 0 < m := by omega
  obtain ⟨n₀,hn₀,hρ,hall⟩ := exists_uniform_walsh_decay.{u,u} m (12*Ddual) Dprimal
    (by linarith) hDp hcut hcutm hsize
  have hbound (N : ℕ) : walshNorm N (ContinuousLinearMap.id ℝ X) ≤ 2*uniformDecayRate m n₀ N := by
    have hρ0 : 0 ≤ uniformDecayRate m n₀ N := by unfold uniformDecayRate; positivity
    apply walshNorm_le_of_bound _ (by positivity)
    intro f
    let E := Submodule.span ℝ (Set.range f)
    let : FiniteDimensional ℝ E := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
    obtain ⟨c⟩ := exists_compactDomain_source hm hdual E
    let := c.normedGroup
    let := c.normedSpace
    let := c.completeSpace
    let F : Cube N → c.G := fun u => c.iota ⟨f u, Submodule.subset_span ⟨u,rfl⟩⟩
    have hF (u : Cube N) : ‖F u‖ ≤ ‖f u‖ := by
      calc
        _ ≤ ‖c.iota‖ * ‖(⟨f u, Submodule.subset_span ⟨u,rfl⟩⟩ : E)‖ := c.iota.le_opNorm _
        _ ≤ ‖f u‖ := by
          simpa using mul_le_of_le_one_left (norm_nonneg (f u)) c.norm_iota
    have hJ : walshNorm N c.J ≤ 2*uniformDecayRate m n₀ N := by
      have h := compactMap_walsh_bound hAP c.J c.compact N hρ0
        (fun A hA => (hall c.G X A c.dual_cotype hprimal hA).2 N)
      exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left c.norm_J hρ0])
    have he : operatorWalsh c.J F = operatorWalsh (ContinuousLinearMap.id ℝ X) f := by
      funext v
      unfold operatorWalsh vectorWalsh
      congr 1; funext u
      change character v u • c.J (F u) = character v u • f u
      rw [show c.J (F u) = f u from c.factor ⟨f u,Submodule.subset_span ⟨u,rfl⟩⟩]
    rw [← he]
    exact (operatorWalsh_le_walshNorm c.J F).trans
      (mul_le_mul hJ (cubeL2_mono hF) (cubeL2_nonneg F) (by positivity))
  apply squeeze_zero (fun N => walshNorm_nonneg N _) hbound
  simpa using hρ.const_mul 2

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution.{u} : type_of% @_root_.OAI.Cotype.identity_walsh_decay_of_fixedCotype.{u} := @_root_.OAI.Cotype.identity_walsh_decay_of_fixedCotype.{u}
