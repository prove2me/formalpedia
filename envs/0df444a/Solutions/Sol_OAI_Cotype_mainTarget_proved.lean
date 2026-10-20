-- Prove2me | solution 1 for OAI.Cotype.mainTarget_proved
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:42:40.335967+00:00
-- url     : https://prove2.me/submissions/87bffd81-5ba3-4f64-8189-7e9aa269e6e4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Main.lean:L26-L28
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Cotype.mainTarget_proved.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Cotype_mainTarget_proved) verbatim and is proved by it.
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
import Theorems.Thm_OAI_Cotype_QuadraticTypeBound_one_le
import Theorems.Thm_OAI_Cotype_average_norm_mul_le
import Theorems.Thm_OAI_Cotype_averaged_projection_power_bound_of_sign_deficit
import Theorems.Thm_OAI_Cotype_dualPairing_radProjection
import Theorems.Thm_OAI_Cotype_exists_admissible_cotype_parameters
import Theorems.Thm_OAI_Cotype_exists_dualPairing_norming
import Theorems.Thm_OAI_Cotype_exists_geometric_levels
import Theorems.Thm_OAI_Cotype_exists_sign_of_radius
import Theorems.Thm_OAI_Cotype_exists_type_extrapolation_parameters
import Theorems.Thm_OAI_Cotype_finiteL2Dual_norm
import Theorems.Thm_OAI_Cotype_geometric_block_bound
import Theorems.Thm_OAI_Cotype_geometric_level_card_le
import Theorems.Thm_OAI_Cotype_hasType_of_normalized_bound
import Theorems.Thm_OAI_Cotype_identity_walsh_decay_of_fixedCotype
import Theorems.Thm_OAI_Cotype_kConvex_iff_coordinate_firstCoefficient_bound
import Theorems.Thm_OAI_Cotype_not_uniformL1_of_kConvex
import Theorems.Thm_OAI_Cotype_not_uniformL1_of_nontrivialType
import Theorems.Thm_OAI_Cotype_projectionLinearCoefficient_bound_of_power_gap
import Theorems.Thm_OAI_Cotype_projectionSubset_union
import Theorems.Thm_OAI_Cotype_tuple_dual_lq_le
import Theorems.Thm_OAI_Cotype_uniformL1_iff_cube

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_add_le {n : ℕ} (f g : Cube n → X) :
    cubeL2 X (fun ε => f ε + g ε) ≤ cubeL2 X f + cubeL2 X g := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => f ε + g ε) : PiLp 2 (fun _ : Cube n => X)) =
      toLp 2 f + toLp 2 g := rfl
  rw [he, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

omit [NormedSpace ℝ X] in
theorem cubeL2_sum_le {n : ℕ} {α : Type*} (s : Finset α) (f : α → Cube n → X) :
    cubeL2 X (fun ε => ∑ a ∈ s, f a ε) ≤ ∑ a ∈ s, cubeL2 X (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubeL2, average]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (cubeL2_add_le _ _).trans (add_le_add le_rfl ih)

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

theorem walshOutputs_bddAbove (n : ℕ) (T : X →L[ℝ] Y) : BddAbove (walshOutputs n T) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (operatorWalsh_L2_le T f).trans ((mul_le_mul_of_nonneg_left hf (norm_nonneg T)).trans_eq (mul_one _))

theorem le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) {f : Cube n → X} (hf : cubeL2 X f ≤ 1) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) ⟨f, hf, rfl⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → X) : average (fun a => f (e a)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshDuality ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem dualPairing_bound {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) :
    |dualPairing f g| ≤ cubeL2 X f * cubeL2 (X →L[ℝ] ℝ) g := by
  calc
    _ ≤ average (fun u => |g u (f u)|) := by
      simpa only [dualPairing, Real.norm_eq_abs] using norm_average_le (fun u => g u (f u))
    _ ≤ average (fun u => ‖f u‖ * ‖g u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun u _ => by
        simpa only [Real.norm_eq_abs, mul_comm] using (g u).le_opNorm (f u))
    _ ≤ _ := average_norm_mul_le f g

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionProducts ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionProduct_norm_apply {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (h : ∀ i x, ‖P i x‖ ≤ ‖x‖) (x : X) : ‖projectionProduct P x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih => exact (h 0 _).trans (ih _ (fun i => h i.succ))

theorem projectionSubset_norm_apply {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (h : ∀ i x, ‖P i x‖ ≤ ‖x‖) (ε : Cube n) (x : X) :
    ‖projectionSubset P ε x‖ ≤ ‖x‖ := by
  apply projectionProduct_norm_apply
  intro i z
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp
  · exact h i z

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.UniformL1 ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem not_uniformL1_of_no_cube
    (h : ¬ ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X,
      (∀ u, ‖x u‖ ≤ 1) ∧
      (∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖)) :
    ¬ UniformL1 X := fun hu => h (uniformL1_iff_cube.mp hu)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.BConvexity ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_common_sign_norming {n : ℕ} (x : Fin n → X)
    (hx : ∀ i, ‖x i‖ ≤ 1) (ε : Cube n) {δ : ℝ}
    (hε : (n : ℝ)-δ ≤ ‖rademacherSum X x ε‖) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ ∀ i, 1-δ ≤ φ (sign (ε i) • x i) := by
  obtain ⟨φ,hφ,he⟩ := exists_dual_vector'' ℝ (rademacherSum X x ε)
  have hb i : φ (sign (ε i) • x i) ≤ 1 := by
    apply (le_abs_self _).trans
    have hn : ‖sign (ε i) • x i‖ ≤ 1 := by
      cases ε i <;> simpa using hx i
    exact (φ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hφ).trans hn)
  refine ⟨φ,hφ,fun i => ?_⟩
  have hs : (∑ j, (1-φ (sign (ε j) • x j))) ≤ δ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hv : (∑ j, φ (sign (ε j) • x j)) = ‖rademacherSum X x ε‖ := by
      rw [← map_sum]; exact he
    rw [hv]; linarith
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hb j))
    (Finset.mem_univ i)
  linarith

theorem l1Family_of_all_signs_large {n : ℕ} (x : Fin n → X)
    (hx : ∀ i, ‖x i‖ ≤ 1) {δ : ℝ}
    (h : ∀ ε : Cube n, (n : ℝ)-δ ≤ ‖rademacherSum X x ε‖) :
    L1Family x (1-δ) := by
  classical
  refine ⟨hx,fun a => ?_⟩
  let ε : Cube n := fun i => decide (a i < 0)
  have ha i : |a i| * sign (ε i) = a i := by
    dsimp [ε, sign]
    split_ifs with hi
    · have hi' : a i < 0 := by simpa using hi
      rw [abs_of_neg hi']; ring
    · have hi' : ¬ a i < 0 := by simpa using hi
      rw [abs_of_nonneg (le_of_not_gt hi')]; ring
  obtain ⟨φ,hφ,hv⟩ := exists_common_sign_norming x hx ε (h ε)
  have hb : (1-δ)*∑ i, |a i| ≤ φ (∑ i, a i • x i) := by
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |a i| * φ (sign (ε i) • x i) := by nlinarith [hv i, abs_nonneg (a i)]
      _ = φ (a i • x i) := by rw [← smul_eq_mul, ← map_smul, smul_smul, ha]
  exact hb.trans ((le_abs_self _).trans ((φ.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hφ)))

theorem l1Family_of_not_bConvex (h : ¬ BConvex X) {c : ℝ} (hc : c < 1) (n : ℕ) :
    ∃ x : Fin n → X, L1Family x c := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨fun i => Fin.elim0 i, by simp [L1Family]⟩
  have hh : ¬ ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-(1-c) := by
    intro hh
    exact h ⟨n,Nat.pos_of_ne_zero hn,1-c,sub_pos.mpr hc,hh⟩
  push Not at hh
  obtain ⟨x,hx,hs⟩ := hh
  exact ⟨x, by simpa using l1Family_of_all_signs_large x hx (fun ε => (hs ε).le)⟩

theorem uniformL1_of_not_bConvex (h : ¬ BConvex X) : UniformL1 X :=
  ⟨1/2,by norm_num,fun n => l1Family_of_not_bConvex h (by norm_num) n⟩

theorem bConvex_of_not_uniformL1 (h : ¬ UniformL1 X) : BConvex X := by
  by_contra hb
  exact h (uniformL1_of_not_bConvex hb)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.BConvexQuantitative ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_rademacherSum_le_sum_norm {n : ℕ} (x : Fin n → X) (ε : Cube n) :
    ‖rademacherSum X x ε‖ ≤ ∑ i, ‖x i‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  cases ε i <;> simp

theorem exists_sign_norm_le_sum_sub {n : ℕ} {δ : ℝ}
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    (x : Fin n → X) {m : ℝ} (hm : 0 ≤ m) (hmx : ∀ i, m ≤ ‖x i‖) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (∑ i, ‖x i‖)-m*δ := by
  classical
  let y : Fin n → X := fun i => ‖x i‖⁻¹ • x i
  have hy i : ‖y i‖ ≤ 1 := by
    by_cases hz : x i = 0
    · simp [y,hz]
    · simp only [y,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
      exact le_refl 1
  have hxy i : ‖x i‖ • y i = x i := by
    by_cases hz : x i = 0
    · simp [y,hz]
    · simp [y,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz)]
  obtain ⟨ε,hε⟩ := h y hy
  refine ⟨ε,?_⟩
  have he : rademacherSum X x ε = m • rademacherSum X y ε +
      ∑ i, sign (ε i) • ((‖x i‖-m) • y i) := by
    simp only [rademacherSum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_comm m,← smul_add,← add_smul,add_sub_cancel, hxy]
  have hr : ‖∑ i, sign (ε i) • ((‖x i‖-m) • y i)‖ ≤ ∑ i, (‖x i‖-m) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hb : ‖(‖x i‖-m) • y i‖ ≤ ‖x i‖-m := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hmx i))]
      exact mul_le_of_le_one_right (sub_nonneg.mpr (hmx i)) (hy i)
    cases ε i <;> simpa using hb
  rw [he]
  calc
    _ ≤ ‖m • rademacherSum X y ε‖ + ‖∑ i, sign (ε i) • ((‖x i‖-m) • y i)‖ := norm_add_le _ _
    _ ≤ m*((n : ℝ)-δ) + ∑ i, (‖x i‖-m) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
      exact add_le_add (mul_le_mul_of_nonneg_left hε hm) hr
    _ = _ := by simp [Finset.sum_sub_distrib]; ring

omit [NormedSpace ℝ X] in

theorem average_sq_le_of_one_deficit {n : ℕ} (f : Cube n → X) {S D : ℝ}
    (hD : 0 ≤ D) (hS : ∀ ε, ‖f ε‖ ≤ S)
    (ε : Cube n) (hε : ‖f ε‖ ≤ S-D) :
    average (fun u => ‖f u‖^2) ≤ S^2 - (Fintype.card (Cube n) : ℝ)⁻¹ * D^2 := by
  classical
  have hS0 : 0 ≤ S := (norm_nonneg (f ε)).trans (hS ε)
  have hd u : 0 ≤ S^2-‖f u‖^2 := by nlinarith [hS u,norm_nonneg (f u)]
  have he : D^2 ≤ S^2-‖f ε‖^2 := by nlinarith [norm_nonneg (f ε)]
  have hs := he.trans (Finset.single_le_sum (fun u _ => hd u) (Finset.mem_univ ε))
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Cube n)) : (0 : ℝ) ≤ _))
  have hid : (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, (S^2-‖f u‖^2) =
      S^2-average (fun u => ‖f u‖^2) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      average,smul_eq_mul,mul_sub,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  rw [hid] at hh
  linarith

theorem rademacher_sq_le_of_sign_deficit {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    (x : Fin n → X) {m : ℝ} (hm : 0 ≤ m) (hmx : ∀ i, m ≤ ‖x i‖) :
    cubeL2 X (rademacherSum X x)^2 ≤ (∑ i, ‖x i‖)^2 -
      (Fintype.card (Cube n) : ℝ)⁻¹ * (m*δ)^2 := by
  obtain ⟨ε,hε⟩ := exists_sign_norm_le_sum_sub h x hm hmx
  rw [cubeL2_sq]
  exact average_sq_le_of_one_deficit _ (mul_nonneg hm hδ)
    (norm_rademacherSum_le_sum_norm x) ε hε

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.BConvexBlocking ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem iterated_sign_deficit {n : ℕ} {δ : ℝ} (hδn : δ ≤ (n : ℝ))
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    (k : ℕ) (x : Fin (n^k) → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ ε : Cube (n^k), ‖rademacherSum X x ε‖ ≤ ((n : ℝ)-δ)^k := by
  classical
  induction k with
  | zero =>
      revert x
      change ∀ x : Fin 1 → X, (∀ i, ‖x i‖ ≤ 1) →
        ∃ ε : Cube 1, ‖rademacherSum X x ε‖ ≤ 1
      intro x hx
      refine ⟨fun _ => false,?_⟩
      simpa [rademacherSum] using hx 0
  | succ k ih =>
      revert x
      rw [pow_succ']
      intro x hx
      let e : Fin n × Fin (n^k) ≃ Fin (n*n^k) := finProdFinEquiv
      let y : Fin n → Fin (n^k) → X := fun j i => x (e (j,i))
      have hh j : ∃ ε : Cube (n^k), ‖rademacherSum X (y j) ε‖ ≤ ((n : ℝ)-δ)^k :=
        ih (y j) (fun i => hx (e (j,i)))
      choose ε hε using hh
      let z : Fin n → X := fun j => rademacherSum X (y j) (ε j)
      obtain ⟨η,hη⟩ := exists_sign_of_radius h (pow_nonneg (sub_nonneg.mpr hδn) k) z hε
      let θ : Cube (n*n^k) := fun u => xor (η (e.symm u).1) (ε (e.symm u).1 (e.symm u).2)
      have hsign (a b : Bool) : sign (xor a b) = sign a*sign b := by cases a <;> cases b <;> norm_num
      have he : rademacherSum X x θ = rademacherSum X z η := by
        simp only [rademacherSum,z,y,Finset.smul_sum,smul_smul]
        rw [← e.sum_comp]
        simp only [Fintype.sum_prod_type,θ,e.symm_apply_apply,hsign]
      refine ⟨θ,?_⟩
      rw [he,pow_succ]
      exact hη

theorem not_uniformL1_of_bConvex (hb : BConvex X) : ¬ UniformL1 X := by
  obtain ⟨n,hn,δ,hδ,h⟩ := hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hδn : δ ≤ (n : ℝ) := by
    obtain ⟨ε,hε⟩ := h (fun _ => 0) (by simp)
    simpa [rademacherSum] using hε
  intro hu
  obtain ⟨c,hc,hcX⟩ := hu
  have hq : ((n : ℝ)-δ)/(n : ℝ) < 1 := (div_lt_one hn0).mpr (by linarith)
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hc hq
  obtain ⟨x,hx⟩ := hcX (n^k)
  obtain ⟨ε,hε⟩ := iterated_sign_deficit hδn h k x hx.1
  have hl := hx.2 (fun i => sign (ε i))
  have habs i : |sign (ε i)| = 1 := by cases ε i <;> norm_num
  simp only [habs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    Nat.cast_pow] at hl
  change c*(n : ℝ)^k ≤ ‖rademacherSum X x ε‖ at hl
  have hkn : ((n : ℝ)-δ)^k < c*(n : ℝ)^k := by
    rw [div_pow] at hk
    exact (div_lt_iff₀ (pow_pos hn0 k)).mp hk
  linarith

theorem bConvex_iff_not_uniformL1 : BConvex X ↔ ¬ UniformL1 X :=
  ⟨not_uniformL1_of_bConvex,bConvex_of_not_uniformL1⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionAverages ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projection_weight_total {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Fin n → Ω → ℝ) (hw : ∀ i, ∑ a, w i a = 1) :
    (∑ ω : Fin n → Ω, ∏ i, w i (ω i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp_rw [hw]
  simp

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionSemigroup ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionSemigroup_average {m : ℕ} (P : Fin m → X →L[ℝ] X) (r : ℝ) :
    projectionSemigroup P r = ∑ ε : Cube m, projectionWeight r ε • projectionSubset P ε := by
  have he i : (∑ b : Bool, (if b then 1-r else r) • (if b then P i else 1)) =
      P i+r • (1-P i) := by
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    module
  unfold projectionSemigroup
  simp_rw [← he]
  exact projectionProduct_weighted_sum _ _

theorem projectionWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {m : ℕ} (ε : Cube m) : 0 ≤ projectionWeight r ε := by
  apply Finset.prod_nonneg
  intro i _
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact hr
  · linarith

theorem projectionWeight_sum (r : ℝ) (m : ℕ) :
    (∑ ε : Cube m, projectionWeight r ε) = 1 := by
  unfold projectionWeight
  apply projection_weight_total (fun (_ : Fin m) (b : Bool) => if b then 1-r else r)
  intro i
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  ring

theorem projectionSubset_idempotent {m : ℕ} (P : Fin m → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (ε : Cube m) :
    projectionSubset P ε * projectionSubset P ε = projectionSubset P ε := by
  simpa using projectionSubset_union P hp hc ε ε

theorem projectionSubset_pairwise_commute {m : ℕ} (P : Fin m → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (ε η : Cube m) :
    Commute (projectionSubset P ε) (projectionSubset P η) := by
  show _ * _ = _ * _
  rw [projectionSubset_union P hp hc, projectionSubset_union P hp hc]
  congr 1
  funext i
  exact Bool.or_comm _ _

theorem projectionSemigroup_power_bound_of_sign_deficit {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (h : ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-δ)
    {m : ℕ} (P : Fin m → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i x, ‖P i x‖ ≤ ‖x‖) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (y : X) :
    ‖((1-projectionSemigroup P r)^n) y‖ ≤ ((2 : ℝ)^n-δ/n)*‖y‖ := by
  rw [projectionSemigroup_average]
  exact averaged_projection_power_bound_of_sign_deficit hn h (projectionWeight r)
    (projectionWeight_nonneg hr hr1) (projectionWeight_sum r m) (projectionSubset P)
    (projectionSubset_idempotent P hp hc) (projectionSubset_pairwise_commute P hp hc)
    (projectionSubset_norm_apply P hP) y

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.FixedTypeImprovement ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem sum_sq_le_card_sum_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i)^2 ≤ (s.card : ℝ)*∑ i ∈ s, (a i)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) a

omit [NormedSpace ℝ X] in

theorem sum_norm_sq_le_of_short_coordinate {n : ℕ} (hn : 0 < n)
    (x : Fin n → X) (hx : ∑ i, ‖x i‖^2 = 1)
    (i : Fin n) (hi : ‖x i‖ ≤ 1/(4*(n : ℝ))) :
    (∑ j, ‖x j‖)^2 ≤ (n : ℝ)-1/2 := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxi j : ‖x j‖ ≤ 1 := by
    have hsq := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖x k‖)
      (Finset.mem_univ j)
    rw [hx] at hsq
    nlinarith [norm_nonneg (x j)]
  have hsum : (∑ j, ‖x j‖) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hxi j)
      _ = _ := by simp
  have herase : (Finset.univ.erase i : Finset (Fin n)).card = n-1 := by simp
  have hn1 : (n-1 : ℕ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hcs := sum_sq_le_card_sum_sq (Finset.univ.erase i) (fun j => ‖x j‖)
  rw [herase,hn1] at hcs
  have hs := Finset.sum_erase_add Finset.univ (fun j => ‖x j‖) (Finset.mem_univ i)
  have hs2 := Finset.sum_erase_add Finset.univ (fun j => ‖x j‖^2) (Finset.mem_univ i)
  rw [hx] at hs2
  rw [show (∑ j ∈ Finset.univ.erase i, ‖x j‖) = (∑ j, ‖x j‖)-‖x i‖ by linarith,
    show (∑ j ∈ Finset.univ.erase i, ‖x j‖^2) = 1-‖x i‖^2 by linarith] at hcs
  have hsmall : ‖x i‖ * (n : ℝ) ≤ 1/4 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 4*n)).mp hi
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsum (norm_nonneg (x i))
  have hnsq : 0 ≤ (n : ℝ)*‖x i‖^2 := mul_nonneg hn0.le (sq_nonneg _)
  nlinarith

theorem exists_normalized_quadratic_gap {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (hδ : 0 < δ)
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : Fin n → X, (∑ i, ‖x i‖^2 = 1) →
      cubeL2 X (rademacherSum X x)^2 ≤ (n : ℝ)-η := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let m : ℝ := 1/(4*(n : ℝ))
  let η : ℝ := min (1/2) ((Fintype.card (Cube n) : ℝ)⁻¹*(m*δ)^2)
  have hm : 0 < m := by dsimp [m]; positivity
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min (by norm_num)
    exact mul_pos (inv_pos.mpr (by exact_mod_cast Fintype.card_pos)) (sq_pos_of_pos (mul_pos hm hδ))
  refine ⟨η,hη,fun x hx => ?_⟩
  by_cases hshort : ∃ i, ‖x i‖ ≤ m
  · obtain ⟨i,hi⟩ := hshort
    have hs := sum_norm_sq_le_of_short_coordinate hn x hx i hi
    have hsum0 : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hb := cubeL2_bound hsum0 (norm_rademacherSum_le_sum_norm x)
    have hηhalf : η ≤ 1/2 := min_le_left _ _
    nlinarith [cubeL2_nonneg (rademacherSum X x)]
  · push Not at hshort
    have hb := rademacher_sq_le_of_sign_deficit hδ.le h x hm.le (fun i => (hshort i).le)
    have hcs : (∑ i, ‖x i‖)^2 ≤ (n : ℝ) := by
      simpa [hx] using sum_sq_le_card_sum_sq Finset.univ (fun i => ‖x i‖)
    have hηloss : η ≤ (Fintype.card (Cube n) : ℝ)⁻¹*(m*δ)^2 := min_le_right _ _
    linarith

theorem quadratic_bound_of_normalized {n : ℕ} {A : ℝ}
    (h : ∀ x : Fin n → X, (∑ i, ‖x i‖^2 = 1) →
      cubeL2 X (rademacherSum X x)^2 ≤ A) :
    ∀ x : Fin n → X, cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by
  classical
  intro x
  let S : ℝ := ∑ i, ‖x i‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : S = 0
  · have hx : ∀ i, x i = 0 := by
      intro i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖x j‖)
        (Finset.mem_univ i)
      change ‖x i‖^2 ≤ S at hi
      rw [hz] at hi
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x i)])
    simp [rademacherSum,hx,cubeL2,average]
  have hS0 : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  let r := Real.sqrt S
  have hr : 0 < r := Real.sqrt_pos.mpr hS0
  have hr2 : r^2 = S := Real.sq_sqrt hS
  let y : Fin n → X := fun i => r⁻¹ • x i
  have hy : ∑ i, ‖y i‖^2 = 1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hr.le),mul_pow,
      ← Finset.mul_sum]
    change (r⁻¹)^2*S = 1
    rw [← hr2,← mul_pow,inv_mul_cancel₀ (ne_of_gt hr)]; norm_num
  have he : rademacherSum X y = fun ε => r⁻¹ • rademacherSum X x ε := by
    funext ε
    simp only [y,rademacherSum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  have hh := h y hy
  rw [he,cubeL2_smul,abs_of_nonneg (inv_nonneg.mpr hr.le),mul_pow] at hh
  have hp := mul_le_mul_of_nonneg_left hh (sq_nonneg r)
  have heq : r^2*((r⁻¹)^2*cubeL2 X (rademacherSum X x)^2) =
      cubeL2 X (rademacherSum X x)^2 := by
    rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ (ne_of_gt hr),one_pow,one_mul]
  rw [heq,hr2] at hp
  simpa [S,mul_comm] using hp

theorem fixed_quadratic_improvement_of_bConvex (h : BConvex X) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : ℝ, 0 ≤ A ∧ A < n ∧
      ∀ x : Fin n → X, cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by
  obtain ⟨n,hn,δ,hδ,h⟩ := h
  obtain ⟨η,hη,hηbound⟩ := exists_normalized_quadratic_gap hn hδ h
  let A := max 0 ((n : ℝ)-η)
  have hA : (n : ℝ)-η ≤ A := le_max_right _ _
  refine ⟨n,hn,A,le_max_left _ _,?_,quadratic_bound_of_normalized (fun x hx => (hηbound x hx).trans hA)⟩
  exact max_lt (by exact_mod_cast hn) (by linarith)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.QuadraticTypeTensor ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_rademacher_twist {n : ℕ} (x : Fin n → X) (σ : Cube n) :
    average (fun ε : Cube n => ‖∑ i, (sign (σ i)*sign (ε i)) • x i‖^2) =
      cubeL2 X (rademacherSum X x)^2 := by
  rw [cubeL2_sq]
  simpa only [signCubeTwist,rademacherSum,Equiv.coe_fn_mk,sign_mul_of_xor] using
    average_equiv (signCubeTwist σ) (fun ε => ‖rademacherSum X x ε‖^2)

theorem average_const_value {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average,smul_eq_mul]

theorem quadraticTypeBound_chaos {n m : ℕ} {A B : ℝ} (hA : 0 ≤ A)
    (hn : QuadraticTypeBound X n A) (hm : QuadraticTypeBound X m B)
    (x : Fin n → Fin m → X) :
    average (fun ε : Cube n => average (fun η : Cube m =>
      ‖∑ i, ∑ j, (sign (ε i)*sign (η j)) • x i j‖^2)) ≤
        A*B*∑ i, ∑ j, ‖x i j‖^2 := by
  classical
  rw [average_comm]
  have hin (η : Cube m) : average (fun ε : Cube n =>
      ‖∑ i, ∑ j, (sign (ε i)*sign (η j)) • x i j‖^2) ≤
        A*∑ i, ‖rademacherSum X (x i) η‖^2 := by
    have hh := hn (fun i => rademacherSum X (x i) η)
    simpa only [cubeL2_sq,rademacherSum,Finset.smul_sum,smul_smul] using hh
  have hb := average_mono hin
  have he : average (fun η : Cube m => A*∑ i, ‖rademacherSum X (x i) η‖^2) =
      A*∑ i, cubeL2 X (rademacherSum X (x i))^2 := by
    simp only [cubeL2_sq,average,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro η _
    ring
  rw [he] at hb
  calc
    _ ≤ A*∑ i, cubeL2 X (rademacherSum X (x i))^2 := hb
    _ ≤ A*∑ i, B*∑ j, ‖x i j‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hm (x i))) hA
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem quadraticTypeBound_mul {n m : ℕ} {A B : ℝ} (hA : 0 ≤ A)
    (hn : QuadraticTypeBound X n A) (hm : QuadraticTypeBound X m B) :
    QuadraticTypeBound X (n*m) (A*B) := by
  classical
  intro x
  let e : Fin n × Fin m ≃ Fin (n*m) := finProdFinEquiv
  let f : Cube (n*m) → Cube n → Cube m → ℝ := fun ζ ε η =>
    ‖∑ i, ∑ j, (sign (ε i)*sign (η j)) • (sign (ζ (e (i,j))) • x (e (i,j)))‖^2
  have hbound ζ : average (fun ε => average (f ζ ε)) ≤ A*B*∑ i, ‖x i‖^2 := by
    have hh := quadraticTypeBound_chaos hA hn hm (fun i j => sign (ζ (e (i,j))) • x (e (i,j)))
    have hs : (∑ i, ∑ j, ‖sign (ζ (e (i,j))) • x (e (i,j))‖^2) = ∑ i, ‖x i‖^2 := by
      have hnorm i j : ‖sign (ζ (e (i,j))) • x (e (i,j))‖ = ‖x (e (i,j))‖ := by
        cases ζ (e (i,j)) <;> simp
      simp only [hnorm]
      simpa only [Fintype.sum_prod_type] using e.sum_comp (fun u => ‖x u‖^2)
    simpa only [hs] using hh
  have havg (ε : Cube n) (η : Cube m) : average (fun ζ => f ζ ε η) =
      cubeL2 X (rademacherSum X x)^2 := by
    let σ : Cube (n*m) := fun u => xor (ε (e.symm u).1) (η (e.symm u).2)
    have he : (fun ζ => f ζ ε η) = fun ζ : Cube (n*m) =>
        ‖∑ u, (sign (σ u)*sign (ζ u)) • x u‖^2 := by
      funext ζ
      simp only [f,smul_smul]
      congr 2
      rw [← e.sum_comp]
      simp only [Fintype.sum_prod_type,σ,e.symm_apply_apply,sign_mul_of_xor]
    rw [he]
    exact average_rademacher_twist x σ
  have hall := average_mono hbound
  have he : average (fun ζ => average (fun ε => average (f ζ ε))) =
      cubeL2 X (rademacherSum X x)^2 := by
    rw [average_comm]
    simp_rw [average_comm (fun ζ η => f ζ _ η),havg,average_const_value]
  rw [he,average_const_value] at hall
  exact hall

theorem quadraticTypeBound_one : QuadraticTypeBound X 1 1 := by
  intro x
  have hn (ε : Cube 1) : ‖rademacherSum X x ε‖^2 = ‖x 0‖^2 := by
    simp only [rademacherSum,Fin.sum_univ_one]
    cases ε 0 <;> simp
  simp only [cubeL2_sq,hn,average_const_value,Fin.sum_univ_one,one_mul,le_refl]

theorem quadraticTypeBound_pow {n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (h : QuadraticTypeBound X n A) (k : ℕ) :
    QuadraticTypeBound X (n^k) (A^k) := by
  induction k with
  | zero => simpa using (quadraticTypeBound_one (X := X))
  | succ k ih => simpa [pow_succ'] using quadraticTypeBound_mul hA h ih

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshAmplification ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [NormedSpace ℝ X] [DecidableEq Ω] in
theorem cubeL2_piLp_sq {n : ℕ} (f : Cube n → PiLp 2 (fun _ : Ω => X)) :
    cubeL2 (PiLp 2 (fun _ : Ω => X)) f ^ 2 =
      ∑ a : Ω, cubeL2 X (fun u => f u a) ^ 2 := by
  simp_rw [cubeL2_sq, PiLp.norm_sq_eq_of_L2]
  simp only [average, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.FiniteL2Dual ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω]

theorem probabilityL2Vector_norm {n : ℕ} (f : Cube n → X) :
    ‖probabilityL2Vector f‖ = cubeL2 X f := by
  rw [probabilityL2Vector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    cubeL2_eq_piLp]

theorem probabilityL2Dual_amplification {n : ℕ} (T : X →L[ℝ] Y)
    (f : Cube n → X) (g : Cube n → (Y →L[ℝ] ℝ)) :
    probabilityL2Dual g (l2Amplification T (probabilityL2Vector f)) =
      dualPairing (fun u => T (f u)) g := by
  simp only [probabilityL2Dual, smul_apply, smul_eq_mul, finiteL2Dual_apply,
    l2Amplification_apply, probabilityL2Vector,
    map_smul, Finset.mul_sum, dualPairing, average]
  apply Finset.sum_congr rfl
  intro u _
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by positivity)]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.KConvexDuality ----
namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem probabilityL2Dual_norm {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) :
    ‖probabilityL2Dual g‖ = cubeL2 (X →L[ℝ] ℝ) g := by
  rw [probabilityL2Dual, norm_smul, finiteL2Dual_norm, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), cubeL2_eq_piLp]

theorem cubeL2_dual_le_of_pairing {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ f : Cube n → X, |dualPairing f g| ≤ C*cubeL2 X f) :
    cubeL2 (X →L[ℝ] ℝ) g ≤ C := by
  rw [← probabilityL2Dual_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  let q := Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹)
  have hc : (0 : ℝ) < Fintype.card (Cube n) := by exact_mod_cast Fintype.card_pos
  have hq : q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (inv_pos.mpr hc))
  let f : Cube n → X := fun u => q⁻¹ • z u
  have he : probabilityL2Vector f = z := by
    ext u
    change q • (q⁻¹ • z u) = z u
    rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
  have hv : probabilityL2Dual g (probabilityL2Vector f) = dualPairing f g := by
    have he' := probabilityL2Dual_amplification (ContinuousLinearMap.id ℝ X) f g
    have hid : l2Amplification (ContinuousLinearMap.id ℝ X) (probabilityL2Vector f) = probabilityL2Vector f := by
      ext u; rfl
    rw [hid] at he'
    exact he'
  rw [← he, hv, probabilityL2Vector_norm]
  exact h f

theorem radProjection_dual_bound {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (n : ℕ) (f : Cube n → X), cubeL2 X (radProjection X f) ≤ K*cubeL2 X f) :
    ∀ (n : ℕ) (g : Cube n → (X →L[ℝ] ℝ)),
      cubeL2 (X →L[ℝ] ℝ) (radProjection (X →L[ℝ] ℝ) g) ≤ K*cubeL2 (X →L[ℝ] ℝ) g := by
  intro n g
  apply cubeL2_dual_le_of_pairing _ (mul_nonneg hK (cubeL2_nonneg g))
  intro f
  rw [dualPairing_radProjection]
  exact (dualPairing_bound _ _).trans (by
    have hh := mul_le_mul_of_nonneg_right (h n f) (cubeL2_nonneg g)
    simpa [mul_assoc, mul_right_comm K] using hh)

theorem radProjection_bound_of_dual {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (n : ℕ) (g : Cube n → (X →L[ℝ] ℝ)),
      cubeL2 (X →L[ℝ] ℝ) (radProjection (X →L[ℝ] ℝ) g) ≤ K*cubeL2 (X →L[ℝ] ℝ) g) :
    ∀ (n : ℕ) (f : Cube n → X), cubeL2 X (radProjection X f) ≤ K*cubeL2 X f := by
  intro n f
  obtain ⟨g,hg,he⟩ := exists_dualPairing_norming (radProjection X f)
  have hb := dualPairing_bound f (radProjection (X →L[ℝ] ℝ) g)
  rw [dualPairing_radProjection, he, abs_of_nonneg (cubeL2_nonneg _)] at hb
  have hd := (h n g).trans (mul_le_of_le_one_right hK hg)
  exact hb.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hd (cubeL2_nonneg f))

theorem kConvex_dual_iff : KConvex (X →L[ℝ] ℝ) ↔ KConvex X := by
  constructor
  · rintro ⟨K,hK,h⟩; exact ⟨K,hK,radProjection_bound_of_dual hK h⟩
  · rintro ⟨K,hK,h⟩; exact ⟨K,hK,radProjection_dual_bound hK h⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TypeCotypeDuality ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem dualPairing_rademacherSum {n : ℕ} (x : Fin n → X) (φ : Fin n → (X →L[ℝ] ℝ)) :
    dualPairing (rademacherSum X x) (rademacherSum (X →L[ℝ] ℝ) φ) = ∑ i, φ i (x i) := by
  calc
    _ = ∑ i, φ i (moment X (rademacherSum X x) i) := by
      generalize rademacherSum X x = f
      simp only [dualPairing, rademacherSum, moment, average, map_smul, map_sum,
        sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp only [moment_rademacherSum]

theorem hasCotype_dual_of_hasType {p : ℝ} (h : HasType X p) :
    HasCotype (X →L[ℝ] ℝ) (p/(p-1)) := by
  obtain ⟨hp,hp2,D,hD,h⟩ := h
  have hp1 : 0 < p-1 := by linarith
  have hq2 : 2 ≤ p/(p-1) := (le_div_iff₀ hp1).mpr (by linarith)
  refine ⟨hq2,D,hD,fun n φ => ?_⟩
  apply tuple_dual_lq_le φ hp (by linarith : 1 < p/(p-1))
    (by field_simp [ne_of_gt hp1]; ring) (mul_nonneg hD (cubeL2_nonneg _))
  intro x
  rw [← dualPairing_rademacherSum x φ]
  exact (dualPairing_bound _ _).trans (by
    have hh := mul_le_mul_of_nonneg_right (h n x) (cubeL2_nonneg (rademacherSum (X →L[ℝ] ℝ) φ))
    simpa [mul_assoc, mul_comm, mul_left_comm] using hh)

theorem hasCotype_of_linearIsometry {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (j : X →ₗᵢ[ℝ] Y) {q : ℝ} (h : HasCotype Y q) : HasCotype X q := by
  obtain ⟨hq,C,hC,h⟩ := h
  refine ⟨hq,C,hC,fun n x => ?_⟩
  have he (u : Cube n) : rademacherSum Y (fun i => j (x i)) u = j (rademacherSum X x u) := by
    simp [rademacherSum]
  simpa only [j.norm_map, cubeL2, he] using h n (fun i => j (x i))

theorem hasCotype_of_bidual {q : ℝ}
    (h : HasCotype ((X →L[ℝ] ℝ) →L[ℝ] ℝ) q) : HasCotype X q :=
  hasCotype_of_linearIsometry (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ) h

theorem finiteCotype_pair_of_nontrivialType (hX : NontrivialType X)
    (hY : NontrivialType (X →L[ℝ] ℝ)) :
    FiniteCotype X ∧ FiniteCotype (X →L[ℝ] ℝ) := by
  obtain ⟨p,hp⟩ := hX
  obtain ⟨q,hq⟩ := hY
  exact ⟨⟨q/(q-1),hasCotype_of_bidual (hasCotype_dual_of_hasType hq)⟩,
    ⟨p/(p-1),hasCotype_dual_of_hasType hp⟩⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.GeometricTypeLevels ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
theorem norm_le_one_of_lp_ball {N : ℕ} {p : ℝ} (hp : 0 < p)
    (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1) (i : Fin N) : ‖x i‖ ≤ 1 := by
  have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Real.rpow_nonneg (norm_nonneg (x j)) p)
    (Finset.mem_univ i)
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by norm_num) hp).mp
  simpa only [Real.one_rpow] using hs.trans hx

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TypeExtrapolation ----
namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Cotype
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem finite_geometric_sum_le (s : Finset ℕ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑ k ∈ s, q^k) ≤ (1-q)⁻¹ := by
  classical
  have hgeom (K : ℕ) : (1-q)*(∑ k ∈ Finset.range K, q^k) = 1-q^K := by
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith
  let K := s.sup id+1
  have hs : s ⊆ Finset.range K := by
    intro k hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => pow_nonneg hq k)
  apply hb.trans
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  nlinarith [hgeom K,pow_nonneg hq K]

theorem normalized_type_bound_of_quadratic_powers {n : ℕ} (hn : 0 < n)
    {A p r : ℝ} (hA : 0 ≤ A) (hp : 0 < p) (hr : 1 < r) (hrp : r^p = n)
    (hq : Real.sqrt (A*n)*r⁻¹ < 1)
    (h : ∀ k : ℕ, QuadraticTypeBound X (n^k) (A^k))
    (N : ℕ) (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1) :
    cubeL2 X (rademacherSum X x) ≤
      Real.sqrt (A*n)*(1-Real.sqrt (A*n)*r⁻¹)⁻¹ := by
  classical
  have hr0 : 0 < r := by linarith
  obtain ⟨l,hl⟩ := exists_geometric_levels hr x (norm_le_one_of_lp_ball hp x hx)
  let S : Finset ℕ := Finset.univ.image l
  let f : ℕ → Fin N → X := fun k i => if l i = k then x i else 0
  have hblock (k : ℕ) : cubeL2 X (rademacherSum X (f k)) ≤
      Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := by
    let s : Finset (Fin N) := Finset.univ.filter (fun i => x i ≠ 0 ∧ l i = k)
    have hcard : s.card ≤ n^(k+1) := by
      apply geometric_level_card_le hn hp hr0 hrp x hx s
      intro i hi
      obtain ⟨hi0,hik⟩ := (Finset.mem_filter.mp hi).2
      simpa only [hik] using ((hl i).2 hi0).le
    apply geometric_block_bound hA hr0 (h (k+1)) s hcard (f k)
    · intro i hi
      dsimp [f]
      split_ifs with hik
      · by_contra hi0
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi0,hik⟩)
      · rfl
    · intro i hi
      have hik := (Finset.mem_filter.mp hi).2.2
      simpa only [f,hik,ite_true] using (hl i).1
  have he : rademacherSum X x = fun ε => ∑ k ∈ S, rademacherSum X (f k) ε := by
    funext ε
    simp only [rademacherSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.smul_sum]
    congr 1
    have hi : l i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    simp [f,hi]
  have hq0 : 0 ≤ Real.sqrt (A*n)*r⁻¹ := mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hr0.le)
  rw [he]
  calc
    _ ≤ ∑ k ∈ S, cubeL2 X (rademacherSum X (f k)) := cubeL2_sum_le S _
    _ ≤ ∑ k ∈ S, Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := Finset.sum_le_sum (fun k _ => hblock k)
    _ = Real.sqrt (A*n)*∑ k ∈ S, (Real.sqrt (A*n)*r⁻¹)^k := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_geometric_sum_le S hq0 hq) (Real.sqrt_nonneg _)

theorem nontrivialType_of_bConvex_nontrivial [Nontrivial X] (h : BConvex X) : NontrivialType X := by
  obtain ⟨n,hn,A,hA,hAn,h⟩ := fixed_quadratic_improvement_of_bConvex h
  have hA1 := QuadraticTypeBound.one_le hn h
  have hn1 : 1 < n := by exact_mod_cast (lt_of_le_of_lt hA1 hAn)
  obtain ⟨p,r,hp,hp2,hr,hrp,_,hq⟩ := exists_type_extrapolation_parameters hn1 hA hAn
  have hD : 0 ≤ Real.sqrt (A*n)*(1-Real.sqrt (A*n)*r⁻¹)⁻¹ := by positivity
  refine ⟨p,hasType_of_normalized_bound hp hp2 hD ?_⟩
  exact normalized_type_bound_of_quadratic_powers hn hA (by linarith) hr hrp hq
    (quadraticTypeBound_pow hA h)

theorem nontrivialType_of_bConvex (h : BConvex X) : NontrivialType X := by
  cases subsingleton_or_nontrivial X with
  | inl hzero =>
      let _ := hzero
      refine ⟨2,by norm_num,by norm_num,0,by norm_num,fun n x => ?_⟩
      have hx : ∀ i, x i = 0 := fun i => Subsingleton.elim _ _
      simp [hx,rademacherSum,cubeL2,average]
  | inr hnonzero =>
      let _ := hnonzero
      exact nontrivialType_of_bConvex_nontrivial h

theorem nontrivialType_of_kConvex (h : KConvex X) : NontrivialType X :=
  nontrivialType_of_bConvex (bConvex_of_not_uniformL1 (not_uniformL1_of_kConvex h))

theorem forwardTarget_proved [CompleteSpace X] [Nontrivial X] : ForwardTarget X := by
  intro h
  exact finiteCotype_pair_of_nontrivialType (nontrivialType_of_kConvex h)
    (nontrivialType_of_kConvex (kConvex_dual_iff.mpr h))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TypeUniformL1 ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem nontrivialType_iff_not_uniformL1 : NontrivialType X ↔ ¬ UniformL1 X :=
  ⟨not_uniformL1_of_nontrivialType,fun h => nontrivialType_of_bConvex (bConvex_of_not_uniformL1 h)⟩

theorem nontrivialType_iff_bConvex : NontrivialType X ↔ BConvex X :=
  nontrivialType_iff_not_uniformL1.trans bConvex_iff_not_uniformL1.symm

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TypeL2Amplification ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem quadraticTypeBound_l2Amplification {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] {n : ℕ} {A : ℝ} (h : QuadraticTypeBound X n A) :
    QuadraticTypeBound (PiLp 2 (fun _ : Ω => X)) n A := by
  intro x
  rw [cubeL2_piLp_sq]
  simp_rw [rademacherSum_piLp_apply, PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => h (fun i => x i a))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionL2Gap ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem sign_deficit_of_quadraticTypeBound {n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (h : QuadraticTypeBound X n A) (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ Real.sqrt (A*n) := by
  classical
  have hsum : (∑ i, ‖x i‖^2) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by nlinarith [hx i, norm_nonneg (x i)])
      _ = _ := by simp
  have hb : average (fun ε => ‖rademacherSum X x ε‖^2) ≤ A*n := by
    rw [← cubeL2_sq]
    exact (h x).trans (mul_le_mul_of_nonneg_left hsum hA)
  by_contra hh
  push Not at hh
  have hp ε : A*n < ‖rademacherSum X x ε‖^2 := by
    have hs := Real.sq_sqrt (mul_nonneg hA (Nat.cast_nonneg n))
    nlinarith [hh ε, Real.sqrt_nonneg (A*n), norm_nonneg (rademacherSum X x ε)]
  have hstrict := Finset.sum_lt_sum (fun ε (_ : ε ∈ Finset.univ) => (hp ε).le)
    ⟨fun _ => false, Finset.mem_univ _, hp _⟩
  have hc : (0 : ℝ) < Fintype.card (Cube n) := by exact_mod_cast Fintype.card_pos
  have hmul := mul_lt_mul_of_pos_left hstrict (inv_pos.mpr hc)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at hmul
  exact (not_lt_of_ge hb) hmul

theorem uniform_sign_deficit_l2Amplification (h : BConvex X) :
    ∃ n : ℕ, 0 < n ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω],
      ∀ x : Fin n → PiLp 2 (fun _ : Ω => X), (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum (PiLp 2 (fun _ : Ω => X)) x ε‖ ≤ (n : ℝ)-δ := by
  obtain ⟨n,hn,A,hA,hAn,hgap⟩ := fixed_quadratic_improvement_of_bConvex h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (A*n) < (n : ℝ) := by
    apply (Real.sqrt_lt' hnR).mpr
    nlinarith
  refine ⟨n,hn,(n : ℝ)-Real.sqrt (A*n),sub_pos.mpr hs,?_⟩
  intro Ω _ _ x hx
  simpa only [sub_sub_cancel] using
    sign_deficit_of_quadraticTypeBound hA (quadraticTypeBound_l2Amplification hgap) x hx

theorem uniform_projectionSemigroup_power_gap_l2Amplification (h : NontrivialType X) :
    ∃ n : ℕ, 0 < n ∧ ∃ C : ℝ, 0 ≤ C ∧ C < (2 : ℝ)^n ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (m : ℕ)
        (P : Fin m → PiLp 2 (fun _ : Ω => X) →L[ℝ] PiLp 2 (fun _ : Ω => X)),
        (∀ i, P i * P i = P i) → (∀ i j, Commute (P i) (P j)) →
        (∀ i x, ‖P i x‖ ≤ ‖x‖) → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        ∀ y, ‖((1-projectionSemigroup P r)^n) y‖ ≤ C*‖y‖ := by
  obtain ⟨n,hn,δ,hδ,hgap⟩ := uniform_sign_deficit_l2Amplification (nontrivialType_iff_bConvex.mp h)
  let C : ℝ := max 0 ((2 : ℝ)^n-δ/n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨n,hn,C,le_max_left _ _,?_,?_⟩
  · exact max_lt (by positivity) (sub_lt_self _ (div_pos hδ hnR))
  · intro Ω _ _ m P hp hc hP r hr hr1 y
    exact (projectionSemigroup_power_bound_of_sign_deficit hn (hgap Ω) P hp hc hP hr hr1 y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg y))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CubeCoordinateProjections ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem coordinateReflection_norm {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) : ‖coordinateReflection i f‖ = ‖f‖ :=
  (l2Reindex (signCubeTwist (unitIndex i))).norm_map f

theorem coordinateExpectation_contracts {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) : ‖coordinateExpectation i f‖ ≤ ‖f‖ := by
  change ‖(1/2 : ℝ) • (f+coordinateReflection i f)‖ ≤ ‖f‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have h := norm_add_le f (coordinateReflection i f)
  rw [coordinateReflection_norm] at h
  linarith

theorem coordinateExpectation_idempotent {n : ℕ} (i : Fin n) :
    coordinateExpectation (X := X) i * coordinateExpectation i = coordinateExpectation i := by
  ext f ε
  change (1/2 : ℝ) • ((1/2 : ℝ) • (f ε + f (signCubeTwist (unitIndex i) ε)) +
    (1/2 : ℝ) • (f (signCubeTwist (unitIndex i) ε) +
      f (signCubeTwist (unitIndex i) (signCubeTwist (unitIndex i) ε)))) =
        (1/2 : ℝ) • (f ε + f (signCubeTwist (unitIndex i) ε))
  have he : signCubeTwist (unitIndex i) (signCubeTwist (unitIndex i) ε) = ε :=
    (signCubeTwist (unitIndex i)).left_inv ε
  rw [he]
  module

theorem coordinateExpectation_commute {n : ℕ} (i j : Fin n) :
    Commute (coordinateExpectation (X := X) i) (coordinateExpectation j) := by
  show _ * _ = _ * _
  ext f ε
  simp only [mul_apply_eq_comp, coordinateExpectation_apply]
  have he : signCubeTwist (unitIndex j) (signCubeTwist (unitIndex i) ε) =
      signCubeTwist (unitIndex i) (signCubeTwist (unitIndex j) ε) := by
    funext k
    exact Bool.xor_left_comm _ _ _
  rw [he]
  module

theorem cube_coordinate_semigroup_power_gap (h : NontrivialType X) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 ≤ C ∧ C < (2 : ℝ)^N ∧
      ∀ (n : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
      ∀ f : PiLp 2 (fun _ : Cube n => X),
        ‖((1-projectionSemigroup (coordinateExpectation (X := X)) r)^N) f‖ ≤ C*‖f‖ := by
  obtain ⟨N,hN,C,hC,hC2,hgap⟩ := uniform_projectionSemigroup_power_gap_l2Amplification h
  refine ⟨N,hN,C,hC,hC2,fun n r hr hr1 f => ?_⟩
  exact hgap (Cube n) n coordinateExpectation coordinateExpectation_idempotent
    coordinateExpectation_commute coordinateExpectation_contracts r hr hr1 f

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshMainEstimates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem walshNorm_identity_ge_of_l1_family {n : ℕ} {L : ℝ} (hL : 0 < L)
    (x : Cube n → X) (hx : ∀ u, ‖x u‖ ≤ 1)
    (hlower : ∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖) :
    L⁻¹ ≤ walshNorm n (ContinuousLinearMap.id ℝ X) := by
  have hout (v : Cube n) : L⁻¹ ≤ ‖operatorWalsh (ContinuousLinearMap.id ℝ X) x v‖ := by
    have h := hlower (fun u => (Fintype.card (Cube n) : ℝ)⁻¹ * character v u)
    have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simpa [operatorWalsh, vectorWalsh, average, abs_mul, abs_character,
      abs_of_nonneg (show 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ by positivity),
      Finset.smul_sum, mul_smul, hc] using h
  have h := cubeL2_mono (f := fun _ : Cube n => L⁻¹)
    (g := operatorWalsh (ContinuousLinearMap.id ℝ X) x) (fun v => by
      simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] using hout v)
  have hin := cubeL2_bound (by positivity : (0:ℝ) ≤ 1) hx
  have hnorm : L⁻¹ ≤ cubeL2 X (operatorWalsh (ContinuousLinearMap.id ℝ X) x) := by
    simpa only [cubeL2_const, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] using h
  exact hnorm.trans (le_walshNorm _ hin)

theorem no_uniform_l1_of_walsh_decay
    (hdecay : Filter.Tendsto (fun n => walshNorm n (ContinuousLinearMap.id ℝ X)) Filter.atTop (nhds 0)) :
    ¬ ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X,
      (∀ u, ‖x u‖ ≤ 1) ∧
      (∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖) := by
  rintro ⟨L, hL, h⟩
  have hb : ∀ n, L⁻¹ ≤ walshNorm n (ContinuousLinearMap.id ℝ X) := by
    intro n
    obtain ⟨x, hx, hlower⟩ := h n
    exact walshNorm_identity_ge_of_l1_family hL x hx hlower
  have hzero : L⁻¹ ≤ (0 : ℝ) := ge_of_tendsto' hdecay hb
  exact (not_le_of_gt (inv_pos.mpr hL)) hzero

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.FiniteCotypeBounds ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype

theorem finite_l2_le_lq {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i)
    {q : ℝ} (hq : 2 ≤ q) :
    Real.sqrt (∑ i, x i ^ 2) ≤
      (m : ℝ)^(1/2-1/q) * (∑ i, x i ^ q)^(1/q) := by
  have hq0 : 0 < q := by linarith
  have hqne := ne_of_gt hq0
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := fun i => x i ^ 2) (by linarith : 1 ≤ q/2)
    (fun i hi => sq_nonneg (x i))
  have he (i : Fin m) : (x i ^ 2) ^ (q/2) = x i ^ q := by
    rw [← Real.rpow_two, ← Real.rpow_mul (hx i)]
    congr 1; ring
  simp only [he, Finset.card_univ, Fintype.card_fin] at h
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hs _) h (le_of_lt (one_div_pos.mpr hq0))
  have hp : (q/2)*(1/q) = (1/2 : ℝ) := by field_simp
  have hp' : (q/2-1)*(1/q) = (1/2-1/q : ℝ) := by field_simp
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg m) _)
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) _)),
    ← Real.rpow_mul hs, ← Real.rpow_mul (Nat.cast_nonneg m), hp, hp'] at hr
  simpa only [Real.sqrt_eq_rpow] using hr

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fixedCotypeBound_of_cotype_constant {q C : ℝ} (hq : 2 ≤ q) (hC : 0 ≤ C)
    (h : ∀ (n : ℕ) (x : Fin n → X),
      (∑ i, ‖x i‖ ^ q)^(1/q) ≤ C*cubeL2 X (rademacherSum X x)) (m : ℕ) :
    FixedCotypeBound X m (C*(m : ℝ)^(1/2-1/q)) := by
  refine ⟨mul_nonneg hC (Real.rpow_nonneg (by positivity) _),?_⟩
  intro x
  exact (finite_l2_le_lq (fun i => ‖x i‖) (fun i => norm_nonneg _) hq).trans
    (by simpa [mul_assoc, mul_comm C] using
      mul_le_mul_of_nonneg_left (h m x) (Real.rpow_nonneg (by positivity) (1/2-1/q)))

theorem finiteCotype_fixed_bounds (h : FiniteCotype X) :
    ∃ q C : ℝ, 2 ≤ q ∧ 1 ≤ C ∧ ∀ m,
      FixedCotypeBound X m (C*(m : ℝ)^(1/2-1/q)) := by
  obtain ⟨q,hq,C,hC,hbound⟩ := h
  refine ⟨q,max C 1,hq,le_max_right _ _,?_⟩
  intro m
  apply fixedCotypeBound_of_cotype_constant hq (le_trans (by norm_num) (le_max_right C 1))
  intro n x
  exact (hbound n x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.MainConstruction ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]

theorem identity_walsh_decay_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) :
    Filter.Tendsto (fun N => walshNorm N (ContinuousLinearMap.id ℝ X)) Filter.atTop (nhds 0) := by
  obtain ⟨q,CF,hq,hCF,hF⟩ := finiteCotype_fixed_bounds hX
  obtain ⟨r,CY,hr,hCY,hY⟩ := finiteCotype_fixed_bounds hXd
  obtain ⟨m,hm,hDd,hDp,hcut,hcutm,hsize⟩ := exists_admissible_cotype_parameters q r CF CY hq hr hCF hCY
  exact identity_walsh_decay_of_fixedCotype hAP m (CY*(m : ℝ)^(1/2-1/r))
    (CF*(m : ℝ)^(1/2-1/q)) hDd hDp (hY m) (hF m) hcut hcutm hsize

theorem no_uniform_l1_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) :
    ¬ ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X,
      (∀ u, ‖x u‖ ≤ 1) ∧
      (∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖) :=
  no_uniform_l1_of_walsh_decay (identity_walsh_decay_of_AP_cotype_cotype hAP hX hXd)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.APNontrivialType ----
namespace OAI

noncomputable section
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]

theorem bConvex_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) : BConvex X :=
  bConvex_of_not_uniformL1 (not_uniformL1_of_no_cube
    (no_uniform_l1_of_AP_cotype_cotype hAP hX hXd))

theorem nontrivialType_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) : NontrivialType X :=
  nontrivialType_of_bConvex (bConvex_of_AP_cotype_cotype hAP hX hXd)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.Main ----
namespace OAI

noncomputable section
universe u
namespace Cotype
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem kConvex_of_nontrivialType (h : NontrivialType X) : KConvex X := by
  obtain ⟨N, hN, C, hC, hC2, hgap⟩ := cube_coordinate_semigroup_power_gap h
  obtain ⟨K, hK, hbound⟩ := projectionLinearCoefficient_bound_of_power_gap hN hC hC2
  apply kConvex_iff_coordinate_firstCoefficient_bound.mpr
  refine ⟨K, hK, fun n f => ?_⟩
  exact hbound (PiLp 2 (fun _ : Cube n => X)) n coordinateExpectation
    coordinateExpectation_idempotent coordinateExpectation_commute
    coordinateExpectation_contracts (hgap n) f

theorem kConvex_of_AP_cotype_cotype [Nontrivial X] (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) : KConvex X :=
  kConvex_of_nontrivialType (nontrivialType_of_AP_cotype_cotype hAP hX hXd)

theorem mainTarget_proved [Nontrivial X] : MainTarget X := by
  intro hAP
  exact ⟨forwardTarget_proved, fun ⟨hX, hXd⟩ => kConvex_of_AP_cotype_cotype hAP hX hXd⟩

end Cotype

end

end OAI

-- ---- mission target ----
open OAI OAI.Cotype
open scoped BigOperators
universe u v
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace OAI
namespace Cotype
theorem _root_.solution [Nontrivial X] : MainTarget X := by
  first
    | exact OAI.Cotype.mainTarget_proved E
    | exact OAI.Cotype.mainTarget_proved
    | (apply OAI.Cotype.mainTarget_proved <;> assumption)
    | (intros; apply OAI.Cotype.mainTarget_proved <;> assumption)
end Cotype
end OAI
