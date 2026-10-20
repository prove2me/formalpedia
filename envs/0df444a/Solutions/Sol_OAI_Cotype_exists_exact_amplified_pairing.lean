-- Prove2me | solution 1 for OAI.Cotype.exists_exact_amplified_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:05:27.369421+00:00
-- url     : https://prove2.me/submissions/706e9960-01ef-4961-b918-53047912479b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshExactPairing.lean:L115-L133
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_exact_amplified_pairing. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_exists_walshBilinear_half

-- ---- from OAI.Analysis.Cotype.Cube ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem character_symm (p ε : ι → Bool) : character p ε = character ε p := by
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> cases ε i <;> rfl

end Cotype

end

end OAI

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

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → X) : average (fun a => f (e a)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp]

theorem average_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → X) : average f = average (fun a => average (fun b => f (a,b))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.smul_sum, smul_smul]
  simp [mul_comm]

theorem average_join {n j : ℕ} (f : Cube (n+j) → X) :
    average f = average (fun a => average (fun b => f (cubeJoin n j (a,b)))) := by
  rw [← average_equiv (cubeJoin n j) f, average_prod]

omit [NormedSpace ℝ X] in
theorem cubeL2_join {n j : ℕ} (f : Cube (n+j) → X) :
    cubeL2 X f = cubeL2 ℝ (fun a : Cube n => cubeL2 X
      (fun b : Cube j => f (cubeJoin n j (a,b)))) := by
  simp only [cubeL2, Real.norm_eq_abs, sq_abs]
  simp_rw [Real.sq_sqrt (show 0 ≤ average (fun b : Cube j =>
    ‖f (cubeJoin n j (_,b))‖ ^ 2) from by
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  rw [average_join]

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

omit [NormedSpace ℝ X] in
theorem cubeL2_norms {n : ℕ} (f : Cube n → X) :
    cubeL2 ℝ (fun u => ‖f u‖) = cubeL2 X f := by simp [cubeL2]

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

omit [DecidableEq Ω] in
theorem operatorWalsh_amplification_bound {n : ℕ} (T : X →L[ℝ] Y)
    (f : Cube n → PiLp 2 (fun _ : Ω => X)) :
    cubeL2 (PiLp 2 (fun _ : Ω => Y)) (operatorWalsh (l2Amplification T) f) ≤
      walshNorm n T * cubeL2 (PiLp 2 (fun _ : Ω => X)) f := by
  apply (sq_le_sq₀ (cubeL2_nonneg _)
    (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))).mp
  rw [mul_pow, cubeL2_piLp_sq, cubeL2_piLp_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simp only [operatorWalsh_amplification_apply]
  simpa only [mul_pow] using (sq_le_sq₀ (cubeL2_nonneg _)
    (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))).mpr
      (operatorWalsh_le_walshNorm T (fun u => f u a))

omit [DecidableEq Ω] in
theorem walshNorm_amplification_le (n : ℕ) (T : X →L[ℝ] Y) :
    walshNorm n (l2Amplification (Ω := Ω) T) ≤ walshNorm n T :=
  walshNorm_le_of_bound _ (walshNorm_nonneg n T) (operatorWalsh_amplification_bound T)

omit [NormedSpace ℝ X] in
theorem cubeL2_piLp_single {n : ℕ} (a : Ω) (f : Cube n → X) :
    cubeL2 (PiLp 2 (fun _ : Ω => X)) (fun u => PiLp.single 2 a (f u)) = cubeL2 X f := by
  simp [cubeL2, PiLp.norm_single]

theorem operatorWalsh_amplification_single {n : ℕ} (T : X →L[ℝ] Y)
    (a : Ω) (f : Cube n → X) :
    operatorWalsh (l2Amplification T) (fun u => PiLp.single 2 a (f u)) =
      fun v => PiLp.single 2 a (operatorWalsh T f v) := by
  classical
  funext v
  ext b
  simp only [operatorWalsh_amplification_apply, PiLp.single, ofLp_toLp]
  by_cases h : b = a
  · subst b
    simp
  · simp [h, operatorWalsh, vectorWalsh, average]

theorem walshNorm_amplification [Nonempty Ω] (n : ℕ) (T : X →L[ℝ] Y) :
    walshNorm n (l2Amplification (Ω := Ω) T) = walshNorm n T := by
  apply (walshNorm_amplification_le n T).antisymm
  apply walshNorm_le_of_bound T (walshNorm_nonneg n _)
  intro f
  obtain ⟨a⟩ := ‹Nonempty Ω›
  have h := operatorWalsh_le_walshNorm (l2Amplification T)
    (fun u => PiLp.single 2 a (f u))
  simpa only [operatorWalsh_amplification_single, cubeL2_piLp_single] using h

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

theorem finiteL2Dual_norm_le (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ ≤ ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ :=
  (finiteL2Dual g).opNorm_le_bound (norm_nonneg _) (finiteL2DualLinear_bound g)

theorem probabilityL2Vector_norm {n : ℕ} (f : Cube n → X) :
    ‖probabilityL2Vector f‖ = cubeL2 X f := by
  rw [probabilityL2Vector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    cubeL2_eq_piLp]

theorem probabilityL2Dual_norm_le {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) :
    ‖probabilityL2Dual g‖ ≤ cubeL2 (X →L[ℝ] ℝ) g := by
  rw [probabilityL2Dual, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    cubeL2_eq_piLp]
  exact mul_le_mul_of_nonneg_left (finiteL2Dual_norm_le g) (Real.sqrt_nonneg _)

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

-- ---- from OAI.Analysis.Cotype.Damping ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem character_xor (P ε η : ι → Bool) :
    character P (xorCube ε η) = character P ε * character P η := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases P i <;> simp [xorCube]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshExactPairing ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem average_const_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → X) :
    average (fun a => c • f a) = c • average f := by
  simp only [average, Finset.smul_sum, smul_smul]
  simp only [mul_comm]

theorem average_translate {n : ℕ} (a : Cube n) (f : Cube n → X) :
    average (fun u => f (xorCube a u)) = average f := average_equiv (cubeTranslate a) f

omit [NormedSpace ℝ X] in
theorem cubeL2_translate {n : ℕ} (a : Cube n) (f : Cube n → X) :
    cubeL2 X (fun u => f (xorCube a u)) = cubeL2 X f := by
  exact congrArg Real.sqrt (average_translate a (fun u => ‖f u‖ ^ 2))

theorem character_xor_left {n : ℕ} (a b c : Cube n) :
    character (xorCube a b) c = character a c * character b c := by
  rw [character_symm, character_xor]
  rw [character_symm c a, character_symm c b]

theorem character_pairing_twist {n : ℕ} (u v a b : Cube n) :
    character u b * character a b * character a v =
      character v u * character (xorCube v b) (xorCube u a) := by
  rw [character_xor_left, character_xor, character_xor]
  rw [character_symm v a, character_symm b u, character_symm b a]
  calc
    _ = (character v u * character v u) *
        (character u b * character a b * character a v) := by rw [character_sq, one_mul]
    _ = _ := by ring

theorem twistedPrimal_L2 {n : ℕ} (p : Cube n → X) (u : Cube n) :
    cubeL2 X (twistedPrimal p u) = cubeL2 X p := by
  rw [cubeL2_join]
  have hn (a b : Cube n) : ‖twistedPrimal p u (cubeJoin n n (a,b))‖ = ‖p (xorCube u a)‖ := by
    simp only [twistedPrimal_join, norm_smul, Real.norm_eq_abs, abs_mul, abs_character, one_mul]
  simp only [cubeL2, hn]
  change cubeL2 ℝ (fun a : Cube n => cubeL2 X (fun _ : Cube n => p (xorCube u a))) = _
  simp_rw [cubeL2_const]
  rw [cubeL2_norms, cubeL2_translate]
  rfl

theorem twistedDual_L2 {n : ℕ} (q : Cube n → (Y →L[ℝ] ℝ)) (v : Cube n) :
    cubeL2 (Y →L[ℝ] ℝ) (twistedDual q v) = cubeL2 (Y →L[ℝ] ℝ) q := by
  rw [cubeL2_join]
  have hn (a b : Cube n) : ‖twistedDual q v (cubeJoin n n (a,b))‖ = ‖q (xorCube v b)‖ := by
    simp only [twistedDual_join, norm_smul, Real.norm_eq_abs, abs_character, one_mul]
  simp only [cubeL2, hn]
  change cubeL2 ℝ (fun _ : Cube n => cubeL2 (Y →L[ℝ] ℝ) (fun b : Cube n => q (xorCube v b))) = _
  rw [cubeL2_translate, cubeL2_const, Real.norm_eq_abs, abs_of_nonneg (cubeL2_nonneg _)]
  rfl

theorem twistedPairing {n : ℕ} (T : X →L[ℝ] Y) (p : Cube n → X)
    (q : Cube n → (Y →L[ℝ] ℝ)) (u v : Cube n) :
    dualPairing (fun z => T (twistedPrimal p u z)) (twistedDual q v) =
      walshBilinear T p q * character v u := by
  unfold dualPairing
  rw [average_join]
  simp only [twistedPrimal_join, twistedDual_join, map_smul, smul_apply, smul_eq_mul]
  have he (a b : Cube n) :
      (character u b * character a b) * (character a v * q (xorCube v b) (T (p (xorCube u a)))) =
      character v u * (character (xorCube v b) (xorCube u a) *
        q (xorCube v b) (T (p (xorCube u a)))) := by
    calc
      _ = (character u b * character a b * character a v) *
        q (xorCube v b) (T (p (xorCube u a))) := by ring
      _ = _ := by rw [character_pairing_twist]; ring
  simp_rw [he]
  simp only [← smul_eq_mul, average_const_smul]
  have hv (a : Cube n) :
      average (fun b => character (xorCube v b) (xorCube u a) •
        q (xorCube v b) (T (p (xorCube u a)))) =
      average (fun b => character b (xorCube u a) • q b (T (p (xorCube u a)))) :=
    average_translate v (fun b => character b (xorCube u a) • q b (T (p (xorCube u a))))
  simp_rw [hv]
  have hu :
      average (fun a => average (fun b => character b (xorCube u a) • q b (T (p (xorCube u a))))) =
      average (fun a => average (fun b => character b a • q b (T (p a)))) :=
    average_translate u (fun a => average (fun b => character b a • q b (T (p a))))
  rw [hu]
  simp only [smul_eq_mul, walshBilinear, mul_comm]

theorem exists_exact_amplified_pairing (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ (γ : ℝ)
      (x : Cube n → PiLp 2 (fun _ : Cube (n+n) => X))
      (y : Cube n → (PiLp 2 (fun _ : Cube (n+n) => Y) →L[ℝ] ℝ)),
      walshNorm n T / 2 < γ ∧ 0 < γ ∧
      (∀ u, ‖x u‖ ≤ 1) ∧ (∀ v, ‖y v‖ ≤ 1) ∧
      (∀ u v, y v (l2Amplification T (x u)) = γ * character v u) ∧
      (∀ k, walshNorm k (l2Amplification (Ω := Cube (n+n)) T) = walshNorm k T) := by
  obtain ⟨p, q, hp, hq, hh, hpos⟩ := exists_walshBilinear_half n hT
  refine ⟨walshBilinear T p q, fun u => probabilityL2Vector (twistedPrimal p u),
    fun v => probabilityL2Dual (twistedDual q v), hh, hpos, ?_, ?_, ?_, ?_⟩
  · intro u
    simpa only [probabilityL2Vector_norm, twistedPrimal_L2] using hp
  · intro v
    exact (probabilityL2Dual_norm_le _).trans ((twistedDual_L2 q v).le.trans hq)
  · intro u v
    rw [probabilityL2Dual_amplification, twistedPairing]
  · intro k
    exact walshNorm_amplification k T

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.exists_exact_amplified_pairing := @_root_.OAI.Cotype.exists_exact_amplified_pairing
