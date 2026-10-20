-- Prove2me | solution 1 for OAI.Cotype.GrowthPairingData.tagged_coefficient_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:17:13.615631+00:00
-- url     : https://prove2.me/submissions/5d26f2f5-87d1-4b66-9bae-8a42ea4f3d29

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/TaggedCoefficient.lean:L51-L69
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.GrowthPairingData.tagged_coefficient_extraction. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_fourier_inversion
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

theorem tuplePairing_equivariant (g : WalshSymmetry n) (U V : Fin m → Cube n) (ε δ : Cube m) :
    d.tuplePairing (fun i => primalSymmetry g (U i)) (fun j => dualSymmetry g (V j)) ε δ =
      d.tuplePairing U V ε δ := by
  unfold tuplePairing
  rw [d.P_equivariant, d.Z_equivariant]
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

theorem patternPairing_eq (hn : m+m ≤ n) (S : Fin m × Fin m → Bool)
    (U V : Fin m → Cube n) (hU : BinaryFrame U) (hV : BinaryFrame V)
    (hS : ∀ i j, character (V j) (U i) = sign (S (i,j))) (ε δ : Cube m) :
    d.patternPairing hn S ε δ = d.tuplePairing U V ε δ := by
  let q := signFrameChoice hn S
  obtain ⟨g,hgU,hgV⟩ := walsh_paired_frames_orbit q.U U q.V V q.U_frame hU q.V_frame hV
    (fun i j => (q.pairing i j).trans (hS i j).symm)
  have h := d.tuplePairing_equivariant g q.U q.V ε δ
  rw [show (fun i => primalSymmetry g (q.U i)) = U from funext hgU,
      show (fun j => dualSymmetry g (q.V j)) = V from funext hgV] at h
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

theorem taggedFrames_pairing (u v : Fin m → Cube k) (D : Fin m × Fin m → Bool)
    (i j : Fin m) :
    character (taggedDual v D j) (taggedPrimal u i) = character (v j) (u i) * sign (D (i,j)) := by
  change character (cubeJoin (k+m) m (cubeJoin k m (v j, fun i => D (i,j)), unitIndex j))
    (cubeJoin (k+m) m (cubeJoin k m (u i, unitIndex i), fun _ => false)) = _
  rw [character_join, character_join, character_symm (fun i => D (i,j)), character_unitIndex]
  have hz : character (unitIndex j) (fun _ : Fin m => false) = 1 := by
    simp [character, sign]
  rw [hz, mul_one]

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

theorem fourier_sum {α : Type*} [Fintype α] (f : α → (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun S => ∑ i, f i S) p = ∑ i, fourier (f i) p := by
  simp only [fourier, Finset.sum_mul, average_sum]

theorem fourier_character (p q : ι → Bool) :
    fourier (character p) q = if p = q then 1 else 0 := average_character_mul p q

theorem fourier_translate (f : (ι → Bool) → ℝ) (δ p : ι → Bool) :
    fourier (fun S => f (xorCube δ S)) p = fourier f p * character p δ := by
  have he : (fun S => f (xorCube δ S)) =
      fun S => ∑ q, (fourier f q * character q δ) * character q S := by
    funext S
    rw [← fourier_inversion f (xorCube δ S)]
    simp [character_xor, mul_assoc]
  rw [he, fourier_sum]
  simp_rw [fourier_const_mul, fourier_character]
  simp

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TaggedCoefficient ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {k m : ℕ}

theorem sign_bitEquiv_symm (z : ZMod 2) : sign (bitEquiv.symm z) = binarySign z := by
  obtain ⟨b,rfl⟩ := bitEquiv.surjective z
  rw [Equiv.symm_apply_apply]
  cases b <;> simp [bitEquiv, binaryBit, sign]

theorem freePairingPattern_sign (u v : Fin m → Cube k) (i j : Fin m) :
    sign (freePairingPattern u v (i,j)) = character (v j) (u i) := by
  rw [freePairingPattern, sign_bitEquiv_symm, character_binary_dot]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem tagged_coefficient_extraction (hn : m+m ≤ k+m+m) (P : SignMatrix m)
    (ε δ : Cube m) (u v : Fin m → Cube k) :
    d.coefficientDual P δ v (d.amplifiedOperator (d.coefficientPrimal ε u)) =
      fourier (fun S => d.patternPairing hn S ε δ) P * character P (freePairingPattern u v) := by
  have he (D : SignMatrix m) : d.tuplePairing (taggedPrimal u) (taggedDual v D) ε δ =
      d.patternPairing hn (xorCube (freePairingPattern u v) D) ε δ := by
    apply (d.patternPairing_eq hn _ _ _ (taggedPrimal_frame u) (taggedDual_frame v D) _ ε δ).symm
    intro i j
    rw [taggedFrames_pairing]
    change _ = sign (Bool.xor (freePairingPattern u v (i,j)) (D (i,j)))
    rw [sign_xor, freePairingPattern_sign]
  calc
    _ = average (fun D : SignMatrix m => character P D *
        d.tuplePairing (taggedPrimal u) (taggedDual v D) ε δ) := by
      simp [coefficientDual, coefficientPrimal, tuplePairing, average]
    _ = fourier (fun D => d.patternPairing hn (xorCube (freePairingPattern u v) D) ε δ) P := by
      simp only [he, fourier]
      congr 1; funext D; ring
    _ = _ := fourier_translate (fun S => d.patternPairing hn S ε δ) _ P

end GrowthPairingData

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype OAI.Cotype.GrowthPairingData
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.GrowthPairingData.tagged_coefficient_extraction := @_root_.OAI.Cotype.GrowthPairingData.tagged_coefficient_extraction
