-- Prove2me | solution 1 for OAI.Cotype.GrowthPairingData.normalized_scalar_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:12:56.216927+00:00
-- url     : https://prove2.me/submissions/7ff9f1ba-51ee-425d-a9ac-bccde94d91f8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/GrowthScalarData.lean:L76-L105
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.GrowthPairingData.normalized_scalar_admissible. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_GrowthPairingData_patternDual_odd_bound
import Theorems.Thm_OAI_Cotype_GrowthPairingData_patternPairing_odd_bound
import Theorems.Thm_OAI_Cotype_GrowthPairingData_patternPrimal_odd_bound
import Theorems.Thm_OAI_Cotype_matrixTwist_row_projection
import Theorems.Thm_OAI_Cotype_rowProjection_oddPart
import Theorems.Thm_OAI_Cotype_vectorTwist_first_coefficient
import Theorems.Thm_OAI_Cotype_walsh_paired_frames_orbit

-- ---- from OAI.Analysis.Cotype.Fourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem oddPart_isOdd (f : (ι → Bool) → ℝ) : IsOdd (oddPart f) := by
  intro ε
  simp only [oddPart, negateCube_negateCube]
  ring

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

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

theorem dualSlice_equivariant (g : WalshSymmetry n) (u : Cube n) (V : Fin m → Cube n) (δ : Cube m) :
    d.dualSlice (primalSymmetry g u) (fun i => dualSymmetry g (V i)) δ = d.dualSlice u V δ := by
  unfold dualSlice
  rw [← d.x_equivariant, d.Z_equivariant]
  exact symmetry_pairing_invariant (l2Amplification (Ω := Cube (n+n)) T) g _ _

theorem tuplePairing_primal_moment (U V : Fin m → Cube n) (δ : Cube m) (i : Fin m) :
    moment ℝ (fun ε => d.tuplePairing U V ε δ) i =
      (1/(2*24*Dg*Real.sqrt m)) * d.dualSlice (U i) V δ := by
  change moment ℝ (fun ε => ((d.Z V δ).comp d.amplifiedOperator) (d.P U ε)) i = _
  rw [← moment_clm ((d.Z V δ).comp d.amplifiedOperator) (d.P U) i, d.P_moment, map_smul]
  rfl

theorem tuplePairing_dual_moment (U V : Fin m → Cube n) (ε : Cube m) (j : Fin m) :
    moment ℝ (fun δ => d.tuplePairing U V ε δ) j =
      (1/(2*24*Df*Real.sqrt m)) * d.primalSlice U (V j) ε := by
  let ev := ContinuousLinearMap.apply ℝ ℝ (d.amplifiedOperator (d.P U ε))
  change moment ℝ (fun δ => ev (d.Z V δ)) j = _
  rw [← moment_clm ev (d.Z V) j, d.Z_moment, map_smul]
  rfl

theorem primalSlice_moment (U : Fin m → Cube n) (v : Cube n) (i : Fin m) :
    moment ℝ (d.primalSlice U v) i =
      (1/(2*24*Dg*Real.sqrt m)) * (d.gamma * character v (U i)) := by
  change moment ℝ (fun ε => ((d.y v).comp d.amplifiedOperator) (d.P U ε)) i = _
  rw [← moment_clm ((d.y v).comp d.amplifiedOperator) (d.P U) i, d.P_moment, map_smul]
  change _ * d.y v (l2Amplification (l2Amplification T) (d.x (U i))) = _
  rw [d.exact_pairing]

theorem dualSlice_moment (u : Cube n) (V : Fin m → Cube n) (j : Fin m) :
    moment ℝ (d.dualSlice u V) j =
      (1/(2*24*Df*Real.sqrt m)) * (d.gamma * character (V j) u) := by
  let ev := ContinuousLinearMap.apply ℝ ℝ (d.amplifiedOperator (d.x u))
  change moment ℝ (fun δ => ev (d.Z V δ)) j = _
  rw [← moment_clm ev (d.Z V) j, d.Z_moment, map_smul]
  change _ * d.y (V j) (l2Amplification (l2Amplification T) (d.x u)) = _
  rw [d.exact_pairing]

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

theorem patternDual_eq (hn : 1+m ≤ n) (s : Cube m)
    (u : Cube n) (V : Fin m → Cube n) (hu : BinaryFrame (fun _ : Fin 1 => u))
    (hV : BinaryFrame V) (hs : ∀ j, character (V j) u = sign (s j)) (δ : Cube m) :
    d.patternDual hn s δ = d.dualSlice u V δ := by
  let q := signFrameChoice hn (fun ij : Fin 1 × Fin m => s ij.2)
  obtain ⟨g,hgu,hgV⟩ := walsh_paired_frames_orbit q.U (fun _ : Fin 1 => u) q.V V
    q.U_frame hu q.V_frame hV (fun i j => (q.pairing i j).trans (hs j).symm)
  have h := d.dualSlice_equivariant g (q.U 0) q.V δ
  rw [hgu 0, show (fun j => dualSymmetry g (q.V j)) = V from funext hgV] at h
  exact h.symm

theorem patternPairing_primal_moment (hn : m+m ≤ n) (hd : 1+m ≤ n)
    (S : Fin m × Fin m → Bool) (δ : Cube m) (i : Fin m) :
    moment ℝ (fun ε => d.patternPairing hn S ε δ) i =
      (1/(2*24*Dg*Real.sqrt m)) * d.patternDual hd (fun j => S (i,j)) δ := by
  let q := signFrameChoice hn S
  change moment ℝ (fun ε => d.tuplePairing q.U q.V ε δ) i = _
  rw [d.tuplePairing_primal_moment]
  rw [d.patternDual_eq hd (fun j => S (i,j)) (q.U i) q.V
    (q.U_frame.comp (fun _ : Fin 1 => i) (fun _ _ _ => Subsingleton.elim _ _))
    q.V_frame (q.pairing i)]

theorem patternPairing_dual_moment (hn : m+m ≤ n) (hp : m+1 ≤ n)
    (S : Fin m × Fin m → Bool) (ε : Cube m) (j : Fin m) :
    moment ℝ (fun δ => d.patternPairing hn S ε δ) j =
      (1/(2*24*Df*Real.sqrt m)) * d.patternPrimal hp (fun i => S (i,j)) ε := by
  let q := signFrameChoice hn S
  change moment ℝ (fun δ => d.tuplePairing q.U q.V ε δ) j = _
  rw [d.tuplePairing_dual_moment]
  rw [d.patternPrimal_eq hp (fun i => S (i,j)) q.U (q.V j) q.U_frame
    (q.V_frame.comp (fun _ : Fin 1 => j) (fun _ _ _ => Subsingleton.elim _ _))
    (fun i => q.pairing i j)]

theorem patternPrimal_moment (hn : m+1 ≤ n) (s : Cube m) (i : Fin m) :
    moment ℝ (d.patternPrimal hn s) i =
      (1/(2*24*Dg*Real.sqrt m)) * (d.gamma * sign (s i)) := by
  let q := signFrameChoice hn (fun ij : Fin m × Fin 1 => s ij.1)
  change moment ℝ (d.primalSlice q.U (q.V 0)) i = _
  rw [d.primalSlice_moment, q.pairing]

theorem patternDual_moment (hn : 1+m ≤ n) (s : Cube m) (j : Fin m) :
    moment ℝ (d.patternDual hn s) j =
      (1/(2*24*Df*Real.sqrt m)) * (d.gamma * sign (s j)) := by
  let q := signFrameChoice hn (fun ij : Fin 1 × Fin m => s ij.2)
  change moment ℝ (d.dualSlice (q.U 0) q.V) j = _
  rw [d.dualSlice_moment, q.pairing]

end GrowthPairingData
end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionCoefficients ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem fourier_const_mul (f : (ι → Bool) → ℝ) (a : ℝ) (p : ι → Bool) :
    fourier (fun S => a * f S) p = a * fourier f p := by
  simp only [fourier, average, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternNormalization ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {α : Type*} [Fintype α]

theorem average_mul_left (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := average_const_smul c f

theorem average_mul_right (f : α → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := average_smul_const f c

theorem average_sub_real (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_div_real (f : α → ℝ) (c : ℝ) :
    average (fun x => f x / c) = average f / c := by
  simp only [div_eq_mul_inv, average_mul_right]

theorem average_const_real [Nonempty α] (c : ℝ) : average (fun _ : α => c) = c := by
  simp [average]

theorem abs_average_le_const [Nonempty α] (f : α → ℝ) {M : ℝ}
    (hf : ∀ a, |f a| ≤ M) : |average f| ≤ M := by
  calc
    _ ≤ average (fun a => |f a|) := by simpa only [Real.norm_eq_abs] using norm_average_le f
    _ ≤ average (fun _ : α => M) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hf a)) (by positivity)
    _ = M := average_const_real M

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem xorCube_negate_right (a b : ι → Bool) :
    xorCube a (negateCube b) = negateCube (xorCube a b) := by
  funext i; simp [xorCube, negateCube]

theorem oddPart_vectorTwist {m : ℕ} (φ : Cube m → Cube m → ℝ) (s : Cube m) :
    oddPart (vectorTwist φ) s = average (fun ε => oddPart (fun s => φ s ε) (xorCube ε s)) := by
  simp only [oddPart, vectorTwist, xorCube_negate_right, average_div_real, average_sub_real]

theorem oddPart_matrixTwist {m : ℕ} (Φ : SignMatrix m → Cube m → Cube m → ℝ) (S : SignMatrix m) :
    oddPart (matrixTwist Φ) S =
      average (fun ε => average (fun δ => oddPart (fun S => Φ S ε δ) (dampedSample ε δ S))) := by
  simp only [oddPart, matrixTwist, dampedSample, xorCube_negate_right,
    average_div_real, average_sub_real]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternProjections ----
namespace OAI

noncomputable section

namespace Cotype
variable {m : ℕ}

theorem columnProjection_oddPart (F : SignMatrix m → ℝ) (j : Fin m) (S : SignMatrix m) :
    columnProjection (oddPart F) j S = columnProjection F j S := by
  exact rowProjection_oddPart (fun R => F (transposeCube R)) j (transposeCube S)

theorem matrixTwist_transpose_swap (Φ : SignMatrix m → Cube m → Cube m → ℝ) (S : SignMatrix m) :
    matrixTwist (fun R ε δ => Φ (transposeCube R) δ ε) S = matrixTwist Φ (transposeCube S) := by
  unfold matrixTwist
  rw [average_comm]
  congr 1; funext ε
  congr 1; funext δ
  have he : transposeCube (dampedSample δ ε S) = dampedSample ε δ (transposeCube S) := by
    funext ij
    simp [transposeCube, dampedSample, xorCube, rowCube, columnCube, Bool.xor_left_comm]
  exact congrArg (fun R => Φ R ε δ) he

theorem matrixTwist_column_projection (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (φ : Cube m → Cube m → ℝ) (b : ℝ)
    (hm : ∀ S ε j, moment ℝ (fun δ => Φ S ε δ) j = b * φ (fun i => S (i,j)) ε)
    (j : Fin m) (S : SignMatrix m) :
    columnProjection (matrixTwist Φ) j S = b * oddPart (vectorTwist φ) (fun i => S (i,j)) := by
  have h := matrixTwist_row_projection (fun R ε δ => Φ (transposeCube R) δ ε) φ b
    (fun R δ i => hm (transposeCube R) δ i) j (transposeCube S)
  simp only [rowProjection, matrixTwist_transpose_swap] at h
  exact h

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.GrowthScalarData ----
namespace OAI

noncomputable section

namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n m k : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

theorem normalizedPrimal_coefficient (hn : m+1 ≤ n) (i : Fin m) :
    fourier (d.normalizedPrimal hn) (unitIndex i) = 1/(2*24*Dg*Real.sqrt m) := by
  unfold normalizedPrimal
  rw [fourier_const_mul, vectorTwist_first_coefficient (d.patternPrimal hn)
    ((1/(2*24*Dg*Real.sqrt m))*d.gamma) (fun s i => by rw [d.patternPrimal_moment]; ring)]
  rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt d.gamma_pos), mul_one]

theorem normalizedDual_coefficient (hn : 1+m ≤ n) (i : Fin m) :
    fourier (d.normalizedDual hn) (unitIndex i) = 1/(2*24*Df*Real.sqrt m) := by
  unfold normalizedDual
  rw [fourier_const_mul, vectorTwist_first_coefficient (d.patternDual hn)
    ((1/(2*24*Df*Real.sqrt m))*d.gamma) (fun s i => by rw [d.patternDual_moment]; ring)]
  rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt d.gamma_pos), mul_one]

theorem normalizedMatrix_row (hn : m+m ≤ n) (hd : 1+m ≤ n) (i : Fin m) (S : SignMatrix m) :
    rowProjection (d.normalizedMatrix hn) i S =
      (1/(2*24*Dg*Real.sqrt m)) * d.normalizedDual hd (fun j => S (i,j)) := by
  calc
    _ = d.gamma⁻¹ * rowProjection (oddPart (matrixTwist (d.patternPairing hn))) i S := by
      simp only [rowProjection, normalizedMatrix, ← average_mul_left]
      congr 1; funext σ; ring
    _ = _ := by
      rw [rowProjection_oddPart, matrixTwist_row_projection (d.patternPairing hn) (d.patternDual hd)
        (1/(2*24*Dg*Real.sqrt m)) (fun S δ i => d.patternPairing_primal_moment hn hd S δ i)]
      unfold normalizedDual
      ring

theorem normalizedMatrix_column (hn : m+m ≤ n) (hp : m+1 ≤ n) (j : Fin m) (S : SignMatrix m) :
    columnProjection (d.normalizedMatrix hn) j S =
      (1/(2*24*Df*Real.sqrt m)) * d.normalizedPrimal hp (fun i => S (i,j)) := by
  calc
    _ = d.gamma⁻¹ * columnProjection (oddPart (matrixTwist (d.patternPairing hn))) j S := by
      simp only [columnProjection, normalizedMatrix, ← average_mul_left]
      congr 1; funext τ; ring
    _ = _ := by
      rw [columnProjection_oddPart, matrixTwist_column_projection (d.patternPairing hn) (d.patternPrimal hp)
        (1/(2*24*Df*Real.sqrt m)) (fun S ε j => d.patternPairing_dual_moment hn hp S ε j)]
      unfold normalizedPrimal
      ring

variable (d : GrowthPairingData T (k+m+m) m Dg Df)

private theorem normalized_value_bound {x : ℝ}
    (hx : |x| ≤ walshNorm k T)
    (hslow : walshNorm k T ≤ 2 * walshNorm (k+m+m) T) : |d.gamma⁻¹ * x| ≤ 4 := by
  rw [abs_mul, abs_of_pos (inv_pos.mpr d.gamma_pos)]
  have hw : walshNorm k T ≤ 4*d.gamma := by linarith [d.gamma_half]
  calc
    _ ≤ d.gamma⁻¹ * (4*d.gamma) :=
      mul_le_mul_of_nonneg_left (hx.trans hw) (le_of_lt (inv_pos.mpr d.gamma_pos))
    _ = 4 := by rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt d.gamma_pos), mul_one]

theorem normalized_scalar_admissible (hm : 0 < m)
    (hn : m+m ≤ k+m+m) (hp : m+1 ≤ k+m+m) (hd : 1+m ≤ k+m+m)
    (hslow : walshNorm k T ≤ 2 * walshNorm (k+m+m) T) :
    ScalarAdmissible m (1/(2*24*Dg*Real.sqrt m)) (1/(2*24*Df*Real.sqrt m))
      (d.normalizedMatrix hn) (d.normalizedPrimal hp) (d.normalizedDual hd) := by
  refine ⟨?_,?_,?_,?_,?_,?_,d.normalizedPrimal_coefficient hp,
    d.normalizedDual_coefficient hd,d.normalizedMatrix_row hn hd,d.normalizedMatrix_column hn hp⟩
  · intro S; unfold normalizedMatrix; rw [oddPart_isOdd]; ring
  · intro s; unfold normalizedPrimal; rw [oddPart_isOdd]; ring
  · intro s; unfold normalizedDual; rw [oddPart_isOdd]; ring
  · intro S
    apply d.normalized_value_bound (hslow := hslow)
    rw [oddPart_matrixTwist]
    apply abs_average_le_const
    intro ε
    apply abs_average_le_const
    intro δ
    exact d.patternPairing_odd_bound hn _ ε δ
  · intro s
    apply d.normalized_value_bound (hslow := hslow)
    rw [oddPart_vectorTwist]
    apply abs_average_le_const
    intro ε
    exact d.patternPrimal_odd_bound hm hp _ ε
  · intro s
    apply d.normalized_value_bound (hslow := hslow)
    rw [oddPart_vectorTwist]
    apply abs_average_le_const
    intro δ
    exact d.patternDual_odd_bound hm hd _ δ

end GrowthPairingData
end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype OAI.Cotype.GrowthPairingData


theorem solution : type_of% @_root_.OAI.Cotype.GrowthPairingData.normalized_scalar_admissible := @_root_.OAI.Cotype.GrowthPairingData.normalized_scalar_admissible
