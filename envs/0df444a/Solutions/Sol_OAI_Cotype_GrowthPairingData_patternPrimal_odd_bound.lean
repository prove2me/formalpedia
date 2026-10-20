-- Prove2me | solution 1 for OAI.Cotype.GrowthPairingData.patternPrimal_odd_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:37:08.439012+00:00
-- url     : https://prove2.me/submissions/d7c20ebc-c248-40c8-993d-ac4ab8e2e1c1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/OddPatternBounds.lean:L98-L111
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.GrowthPairingData.patternPrimal_odd_bound. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_average_norm_mul_le
import Theorems.Thm_OAI_Cotype_walsh_paired_frames_orbit

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

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem character_join {n j : ℕ} (a c : Cube n) (b d : Cube j) :
    character (cubeJoin n j (a,b)) (cubeJoin n j (c,d)) =
      character a c * character b d := by
  simp [character, Fin.prod_univ_add]

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

theorem walshBilinear_eq_pairing {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) :
    walshBilinear T f g = dualPairing (operatorWalsh T f) g := by
  rw [walshBilinear, average_comm]
  simp [dualPairing, operatorWalsh, vectorWalsh, average]

theorem walshBilinear_bound {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) :
    |walshBilinear T f g| ≤ walshNorm n T * cubeL2 X f * cubeL2 (Y →L[ℝ] ℝ) g := by
  rw [walshBilinear_eq_pairing]
  exact (dualPairing_bound _ _).trans
    (mul_le_mul_of_nonneg_right (operatorWalsh_le_walshNorm T f) (cubeL2_nonneg g))

theorem walshBilinear_unit_bound {n : ℕ} (T : X →L[ℝ] Y)
    {f : Cube n → X} {g : Cube n → (Y →L[ℝ] ℝ)}
    (hf : cubeL2 X f ≤ 1) (hg : cubeL2 (Y →L[ℝ] ℝ) g ≤ 1) :
    |walshBilinear T f g| ≤ walshNorm n T := by
  have h := walshBilinear_bound T f g
  have hfg : cubeL2 X f * cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 :=
    (mul_le_mul hf hg (cubeL2_nonneg g) (by positivity)).trans_eq (one_mul 1)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hfg (walshNorm_nonneg n T)])

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.DualAction ----
namespace OAI

noncomputable section
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {Γ : Type*} [Group Γ]

theorem dualAction_pairing (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (g : Γ) (f : X →L[ℝ] ℝ) (x : X) :
    dualAction ρ g f (ρ g x) = f x := by
  change f ((ρ g).symm (ρ g x)) = _
  simp

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.EquivariantPairing ----
namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

variable {n : ℕ}
theorem symmetry_pairing_invariant (T : X →L[ℝ] Y) (g : WalshSymmetry n)
    (x : SymmetryL2 n X) (y : SymmetryL2 n Y →L[ℝ] ℝ) :
    dualAction (rightTranslation (X := Y)) g y
      (l2Amplification T (rightTranslation g x)) = y (l2Amplification T x) := by
  have he : l2Amplification T (rightTranslation g x) = rightTranslation g (l2Amplification T x) := by
    ext R; rfl
  rw [he, dualAction_pairing]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.GrowthTuplePairing ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {n m : ℕ} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

theorem primalSlice_equivariant (g : WalshSymmetry n) (U : Fin m → Cube n) (v : Cube n) (ε : Cube m) :
    d.primalSlice (fun i => primalSymmetry g (U i)) (dualSymmetry g v) ε = d.primalSlice U v ε := by
  unfold primalSlice
  rw [d.P_equivariant, ← d.y_equivariant]
  exact symmetry_pairing_invariant (l2Amplification (Ω := Cube (n+n)) T) g _ _

end GrowthPairingData
end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternPairing ----
namespace OAI

noncomputable section

namespace Cotype

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {n m : ℕ} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

theorem patternPrimal_eq (hn : m+1 ≤ n) (s : Cube m)
    (U : Fin m → Cube n) (v : Cube n) (hU : BinaryFrame U)
    (hv : BinaryFrame (fun _ : Fin 1 => v))
    (hs : ∀ i, character v (U i) = sign (s i)) (ε : Cube m) :
    d.patternPrimal hn s ε = d.primalSlice U v ε := by
  let q := signFrameChoice hn (fun ij : Fin m × Fin 1 => s ij.1)
  obtain ⟨g,hgU,hgv⟩ := walsh_paired_frames_orbit q.U U q.V (fun _ : Fin 1 => v)
    q.U_frame hU q.V_frame hv (fun i j => (q.pairing i j).trans (hs i).symm)
  have h := d.primalSlice_equivariant g q.U (q.V 0) ε
  rw [show (fun i => primalSymmetry g (q.U i)) = U from funext hgU, hgv 0] at h
  exact h.symm

end GrowthPairingData
end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TaggedFrames ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {k m : ℕ}

theorem binaryFrame_of_coordinates {n r : ℕ} (U : Fin r → Cube n) (t : Fin r → Fin n)
    (ht : ∀ i j, binaryBit (U i (t j)) = if i = j then 1 else 0) : BinaryFrame U := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have h := congrFun hc (t j)
  simpa [Finset.sum_apply, ht] using h

theorem taggedPrimal_frame (u : Fin m → Cube k) : BinaryFrame (taggedPrimal u) := by
  apply binaryFrame_of_coordinates _ (fun j => Fin.castAdd m (Fin.natAdd k j))
  intro i j
  simp [taggedPrimal, unitIndex, binaryBit, eq_comm]

theorem taggedDual_frame (v : Fin m → Cube k) (D : Fin m × Fin m → Bool) :
    BinaryFrame (taggedDual v D) := by
  apply binaryFrame_of_coordinates _ (fun j => Fin.natAdd (k+m) j)
  intro i j
  simp [taggedDual, unitIndex, binaryBit, eq_comm]

theorem taggedCovector_frame (hm : 0 < m) (v : Cube k) (s : Cube m) :
    BinaryFrame (fun _ : Fin 1 => taggedCovector hm v s) := by
  exact (taggedDual_frame (fun _ : Fin m => v) (fun ij => s ij.1)).comp
    (fun _ : Fin 1 => (⟨0,hm⟩ : Fin m)) (fun _ _ _ => Subsingleton.elim _ _)

theorem taggedCovector_pairing (hm : 0 < m) (u : Fin m → Cube k) (v : Cube k)
    (s : Cube m) (i : Fin m) :
    character (taggedCovector hm v s) (taggedPrimal u i) = character v (u i) * sign (s i) := by
  change character (cubeJoin (k+m) m (cubeJoin k m (v,s), unitIndex ⟨0,hm⟩))
    (cubeJoin (k+m) m (cubeJoin k m (u i,unitIndex i),fun _ => false)) = _
  rw [character_join, character_join, character_symm s, character_unitIndex]
  have hz : character (unitIndex (⟨0,hm⟩ : Fin m)) (fun _ : Fin m => false) = 1 := by
    simp [character, sign]
  rw [hz, mul_one]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.OddPatternBounds ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem walsh_amplitude_bound {k : ℕ} (T : X →L[ℝ] Y)
    (f : Cube k → X) (g : Cube k → (Y →L[ℝ] ℝ)) (a : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ 1) (hg : ∀ v, ‖g v‖ ≤ 1)
    (ha : ∀ u v, g v (T (f u)) = character v u * a) : |a| ≤ walshNorm k T := by
  have h := walshBilinear_unit_bound T (cubeL2_bound (by positivity) hf)
    (cubeL2_bound (by positivity) hg)
  have he : walshBilinear T f g = a := by
    simp only [walshBilinear, ha, ← mul_assoc, character_sq, one_mul]
    have hc : (Fintype.card (Cube k) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [average]
  rwa [he] at h

theorem norm_half_sub_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖(1/2 : ℝ) • (x-y)‖ ≤ 1 := by
  rw [norm_smul]
  norm_num
  linarith [norm_sub_le x y]

theorem character_one_or_neg_one {k : ℕ} (u v : Cube k) :
    character v u = 1 ∨ character v u = -1 := by
  have h := character_sq v u
  exact mul_self_eq_one_iff.mp h

namespace GrowthPairingData
variable {k m : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem tagged_primal_odd_identity (hm : 0 < m) (hn : m+1 ≤ k+m+m)
    (s : Cube m) (ε : Cube m) (u v : Cube k) :
    (d.primalSlice (taggedPrimal (fun _ => u)) (taggedCovector hm v s) ε -
      d.primalSlice (taggedPrimal (fun _ => u)) (taggedCovector hm v (negateCube s)) ε) / 2 =
    character v u * oddPart (fun s => d.patternPrimal hn s ε) s := by
  have hU := taggedPrimal_frame (fun _ : Fin m => u)
  have hV := taggedCovector_frame hm v
  rcases character_one_or_neg_one u v with hc | hc
  · have hp := d.patternPrimal_eq hn s _ _ hU (hV s)
      (fun i => by rw [taggedCovector_pairing, hc, one_mul]) ε
    have hq := d.patternPrimal_eq hn (negateCube s) _ _ hU (hV (negateCube s))
      (fun i => by rw [taggedCovector_pairing, hc, one_mul]) ε
    rw [← hp, ← hq, hc, one_mul]
    rfl
  · have hp := d.patternPrimal_eq hn (negateCube s) _ _ hU (hV s)
      (fun i => by rw [taggedCovector_pairing, hc]; simp [negateCube]) ε
    have hq := d.patternPrimal_eq hn s _ _ hU (hV (negateCube s))
      (fun i => by rw [taggedCovector_pairing, hc]; simp [negateCube]) ε
    rw [← hp, ← hq, hc]
    unfold oddPart
    ring

theorem patternPrimal_odd_bound (hm : 0 < m) (hn : m+1 ≤ k+m+m)
    (s : Cube m) (ε : Cube m) :
    |oddPart (fun s => d.patternPrimal hn s ε) s| ≤ walshNorm k T := by
  let f := fun u : Cube k => d.P (taggedPrimal (fun _ => u)) ε
  let g := fun v : Cube k => (1/2 : ℝ) •
    (d.y (taggedCovector hm v s) - d.y (taggedCovector hm v (negateCube s)))
  have h := walsh_amplitude_bound d.amplifiedOperator f g
    (oddPart (fun s => d.patternPrimal hn s ε) s)
    (fun u => d.P_norm _ _) (fun v => norm_half_sub_le_one (d.y_norm _) (d.y_norm _))
    (by
      intro u v
      have h := d.tagged_primal_odd_identity hm hn s ε u v
      simpa [f,g,primalSlice, div_eq_mul_inv, mul_comm] using h)
  exact h.trans_eq (d.walsh_norms k)

end GrowthPairingData

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype OAI.Cotype.GrowthPairingData
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.GrowthPairingData.patternPrimal_odd_bound := @_root_.OAI.Cotype.GrowthPairingData.patternPrimal_odd_bound
