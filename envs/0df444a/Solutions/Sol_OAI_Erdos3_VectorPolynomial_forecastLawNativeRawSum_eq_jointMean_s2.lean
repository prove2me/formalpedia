-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastLawNativeRawSum_eq_jointMean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:33:58.61805+00:00
-- url     : https://prove2.me/submissions/3e4ac457-1c8e-43fd-9d9f-c1cd102ab30f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217
import Definitions.Def_OAIE3v2B218
import Definitions.Def_OAIE3v2B232
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastRawSpatialBox_normalized_integral_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SignedSplitCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I J : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [Fintype I] [Fintype J]

theorem signedSplitCoordinates_symm_apply (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F)
    (z : J → R) (w : I → R) :
    (signedSplitCoordinates q s hs bK bI).symm (z, w) =
      (bK.equivFun.symm w).val - s (bI.equivFun.symm z) := by
  change (bK.equivFun.symm w).val + s (bI.equivFun.symm (-z)) = _
  rw [map_neg, map_neg, sub_eq_add_neg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem standardEuclideanLinearEquiv_apply (J : Type*) [Fintype J] (z : J → ℤ) (i : J) :
    (standardEuclideanLinearEquiv J z).val i = (z i : ℝ) := by
  have h := latticeBasisEquiv_coordinates (standardEuclideanLattice J)
    (EuclideanSpace.basisFun J ℝ).toBasis rfl z i
  have he : (latticeBasisEquiv (standardEuclideanLattice J)
      (EuclideanSpace.basisFun J ℝ).toBasis rfl z).val =
      (standardEuclideanLinearEquiv J z).val := rfl
  rw [he] at h
  simpa only [Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using h

theorem standardEuclideanLinearEquiv_eq_point (J : Type*) [Fintype J] (z : J → ℤ) :
    standardEuclideanLinearEquiv J z = standardEuclideanPoint J z := by
  apply Subtype.ext
  ext i
  exact standardEuclideanLinearEquiv_apply J z i

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

variable [Fintype I] [Fintype J]

theorem latticeSignedCoordinates_symm_apply (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ))
    (z : J → ℤ) (w : I → ℤ) :
    ((latticeSignedCoordinates Λ W bW bP).symm (z, w)).val =
      (bW.equivFun.symm w).val.val - (latticeIntegerLift Λ W bP z).val := by
  rw [latticeSignedCoordinates, signedSplitCoordinates_symm_apply]
  simp only [Submodule.coe_sub, Basis.map_equivFun, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rfl

theorem latticeSignedCoordinates_reconstruction (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : Λ) :
    x.val + (latticeIntegerLift Λ W bP (latticeSignedCoordinates Λ W bW bP x).1).val =
      (bW.equivFun.symm (latticeSignedCoordinates Λ W bW bP x).2).val.val := by
  have h := latticeSignedCoordinates_symm_apply Λ W bW bP
    (latticeSignedCoordinates Λ W bW bP x).1 (latticeSignedCoordinates Λ W bW bP x).2
  change ((latticeSignedCoordinates Λ W bW bP).symm (latticeSignedCoordinates Λ W bW bP x)).val = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact eq_sub_iff_add_eq.mp h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

theorem standardLatticeCoordinates_reconstruction (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (β : D → ℤ) :
    (standardEuclideanPoint D β).val +
        (standardLatticeIntegerLift W bP hP
          (fun j => standardLatticeCoordinates W bW bP hP β (Sum.inl j))).val =
      (bW.equivFun.symm (fun i => standardLatticeCoordinates W bW bP hP β (Sum.inr i))).val.val := by
  rw [← standardEuclideanLinearEquiv_eq_point]
  exact latticeSignedCoordinates_reconstruction (standardEuclideanLattice D) W bW
    (integerBasisOfReal (projectedIntegerLattice W) bP hP) (standardEuclideanLinearEquiv D β)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem latticeDeckInteger_coordinates (z : Fin n → ℤ) (w : I → ℤ) :
    standardLatticeCoordinates W bW b hb (latticeDeckInteger W bW b hb z w) =
      Sum.elim z w := LinearEquiv.apply_symm_apply _ _

theorem latticeDeckInteger_reconstruction (z : Fin n → ℤ) (w : I → ℤ) :
    (standardEuclideanPoint D (latticeDeckInteger W bW b hb z w)).val +
        (standardLatticeIntegerLift W b hb z).val =
      (bW.equivFun.symm w).val.val := by
  have h := standardLatticeCoordinates_reconstruction W bW b hb
    (latticeDeckInteger W bW b hb z w)
  simpa only [latticeDeckInteger_coordinates, Sum.elim_inl, Sum.elim_inr] using h

theorem normalizedLatticePoint_linear_lift (x : W × (Fin n → ℤ)) :
    normalizedLatticePoint W b x = x.1.val +
      (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val := by
  rw [normalizedLatticePoint_eq_sheet W b hb, standardLatticeIntegerLift_projection]
  unfold latticeSheetPoint
  rw [latticeBasisEquiv_synthesis]

theorem normalizedDeckPoint_identity (x : W × (Fin n → ℤ)) (w : I → ℤ) :
    (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val).val =
      normalizedLatticePoint W b x +
        (standardEuclideanPoint D (latticeDeckInteger W bW b hb x.2 w)).val := by
  have hβ := latticeDeckInteger_reconstruction W bW b hb x.2 w
  have hs := W.starProjection_add_starProjection_orthogonal
    (standardLatticeIntegerLift W b hb x.2).val
  change (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val = _ at hs
  rw [normalizedLatticePoint_linear_lift W b hb]
  change x.1.val - (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (bW.equivFun.symm w).val.val = _
  rw [← hs] at hβ
  rw [← hβ]
  abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem forecastJointGridScale_pos {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i) {τ : ℝ} (hτ : 0 < τ) :
    ∀ j, 0 < forecastJointGridScale U basis R L physicalN τ j := by
  intro j
  cases j with
  | inl i =>
    have hi : 0 < (physicalN i : ℝ) := by exact_mod_cast hN i
    change 0 < τ * physicalN i / 8
    positivity
  | inr a => exact allocatedActiveIntegerGridScale_pos U basis hR L a

omit [Fintype X] in
theorem forecastJointGrid_normalized_join (R : Fin m → ℝ) (L : ℕ)
    (physicalN : X → ℕ) (τ : ℝ) (base u : X → ℤ)
    (v : AllocatedActiveIntegerAxis U basis L → ℤ) :
    (fun j => ((Sum.elim u v j : ℤ) - forecastJointGridCenter U basis L base j : ℝ) /
      forecastJointGridScale U basis R L physicalN τ j) =
    Sum.elim (fun i => ((u i : ℝ) - base i) / (τ * physicalN i / 8))
      (fun a => (v a : ℝ) / allocatedActiveIntegerGridScale U basis R L a) := by
  funext j
  cases j <;> simp [forecastJointGridScale, forecastJointGridCenter]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastJointNativeResidue
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)
local notation "short" => allocatedShortAxis (I := I) U basis L

theorem forecastJointNativeResidue_integer (q : ℕ)
    (u : X → ℤ) (ks : AllocatedShortIntegerAxis U basis L → ℤ)
    (ka : AllocatedActiveIntegerAxis U basis L → ℤ) (deck : ∀ j, E j → ℤ) :
    forecastJointNativeResidue (I := I) U basis L (fun j e => (deck j e : ZMod q))
        (Sum.elim (fun x => (u x : ZMod q)) (fun a => (ka a : ZMod q))) =
      fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis L ks ka ⟨j, i⟩)
          (deck j)) output : ZMod q) := by
  funext output
  rcases output with ⟨j, x | e | i⟩
  · rfl
  · rfl
  · change (ka ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩ : ZMod q) =
      (forecastIntegerAxisMerge U basis L ks ka ⟨j, i.val⟩ : ZMod q)
    rw [forecastIntegerAxisMerge_active U basis L ks ka ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

omit [∀ j, Fintype (I j)] in
theorem forecastActiveCoordinateJoin_mixed (R : Fin m → ℝ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastNormalizedActiveCoordinates (allocatedShortAxis (I := I) U basis L)
        (allocatedFullMixedSiteValue (R := R) U basis w) =
      forecastActiveCoordinateJoin U basis L
        (fun a => (w a.1).1 a.2 / R a.1)
        (fun a => ((w a.val.1).2 a.val.2 : ℝ) /
          allocatedActiveIntegerGridScale U basis R L a) := by
  funext a
  rcases a with ⟨⟨⟨j, i | i⟩, ha⟩, u⟩
  · rfl
  · change ((w j).2 i : ℝ) / (basisAxisScale (basis j) i : ℝ) / R j =
      ((w j).2 i : ℝ) / (R j * (basisAxisScale (basis j) i : ℝ))
    rw [div_div, mul_comm (R j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

theorem forecastNativeAmbientLinear_mixed (hR : ∀ j, R j ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastNativeAmbientLinear U b o R (allocatedFullMixedSiteValue (R := R) U b w) =
      fun a : Σ j, J j => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 := by
  have hrow (j : Fin m) : forecastNativeMixedRow (I := I) (n := n) R j
      (allocatedFullMixedSiteValue (R := R) U b w) =
      ((w j).1, fun i => ((w j).2 i : ℝ) / basisAxisScale (b j) i) := by
    apply Prod.ext <;> funext i
    · change R j * ((w j).1 i / R j) = _
      exact mul_div_cancel₀ _ (hR j)
    · change R j * ((((w j).2 i : ℝ) / basisAxisScale (b j) i) / R j) = _
      exact mul_div_cancel₀ _ (hR j)
  funext a
  change mixedRealPoint _ _ _ (forecastNativeMixedRow R a.1 _) a.2 = _
  rw [hrow, mixedRealPoint_integer]

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Active" => {a : LayerSamplerAxis I n // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)

omit [∀ j, Fintype (I j)] in
theorem forecastNativeFillAxes_restrict (v : LayerSamplerAxis I n → ℝ) :
    forecastNativeFillAxes P (fun a => v a.val) (fun a => v a.1.val) = v := by
  funext a
  simp only [forecastNativeFillAxes]
  split <;> rfl

variable {X : Type*} [Fintype X]
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

omit [Fintype X] in
theorem forecastNativeSpatialInverse_integer (base u : X → ℤ) (N : X → ℕ)
    (hN : ∀ x, 0 < N x) {τ : ℝ} (hτ : τ ≠ 0) :
    forecastNativeSpatialInverse (fun x => (base x : ℝ) / N x) τ
      (fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)) =
      fun x => (u x : ℝ) / N x := by
  funext x
  have hn : (N x : ℝ) ≠ 0 := by exact_mod_cast (hN x).ne'
  dsimp only [forecastNativeSpatialInverse]
  field_simp
  ring

theorem forecastNativeTorusInverse_mixed (hR : ∀ j, R j ≠ 0)
    (d : ℕ) [NeZero d] (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
    (β : (Σ j, J j) → ℤ) :
    forecastNativeTorusInverse U b o R P d (fun a => (β a : ZMod d))
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.val)
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      fun a : Σ j, J j => (((normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 + β a) / d : ℝ) : UnitAddCircle) := by
  unfold forecastNativeTorusInverse
  rw [forecastNativeFillAxes_restrict, forecastNativeAmbientLinear_mixed U b o R hR w]
  funext a
  rw [ZMod.toAddCircle_intCast, ← AddCircle.coe_add, ← add_div]

theorem forecastNativeCoveredChart_ambient
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
    (deck : ∀ j, Q j → ℤ) (a : Σ j, J j) :
    subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
      (normalizedCoveredChart (euclideanSubspace (U a.1)) (b a.1) (hb a.1) (bW a.1) d
        (orthonormalMixedChart (o a.1) (w a.1), integerResidueMap (Q a.1) d (deck a.1)))) a.2 =
      (((normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 +
        (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
          (w a.1).2 (deck a.1) a.2 : ℝ)) / d : ℝ) : UnitAddCircle) := by
  rw [normalizedCoveredChart, normalizedCoverLift_add_deck,
    euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk]
  change (((d : ℝ)⁻¹ * _ : ℝ) : UnitAddCircle) = _
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  rw [div_eq_inv_mul]
  congr 1
  exact congrArg (fun v : EuclideanSpace ℝ (J a.1) => v a.2)
    (normalizedDeckPoint_identity (euclideanSubspace (U a.1)) (bW a.1)
      (b a.1) (hb a.1) _ (deck a.1))

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem forecastPullback_mixed
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (hR : ∀ j, R j ≠ 0) (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (β : (Σ j, J j) → ℤ) :
    W.forecastPullback U b o R P (fun x => (u x : ZMod W.modulus))
      (fun a => (β a : ZMod W.cover)) (fun x => (base x : ℝ) / N x) τ
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.val)
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      W.mask (fun x => (u x : ZMod W.modulus)) *
        W.smooth (fun x => (u x : ℝ) / N x,
          fun a : Σ j, J j => (((normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
            (orthonormalMixedChart (o a.1) (w a.1)) a.2 + β a) / W.cover : ℝ) : UnitAddCircle)) := by
  unfold forecastPullback
  rw [forecastNativeSpatialInverse_integer base u N hN hτ,
    forecastNativeTorusInverse_mixed U b o R P hR]

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical Matrix

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

theorem forecastNativeSpatialResidue_reduction (hm : 0 < m) {q d : ℕ} (hd : d ∣ q)
    (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
    zmodPiReduction hd (forecastNativeSpatialResidue inactive hm
      (fun a => (forecastCongruenceOutput (R := ℤ) inactive u label a : ZMod q))) =
      fun x => (u x : ZMod d) := by
  funext x
  exact map_intCast (ZMod.castHom hd (ZMod d)) (u x)

theorem forecastNativeCoordinateResidue_output (q : ℕ) (u : X → ℤ)
    (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
    forecastNativeCoordinateResidue inactive q (fun j i => label j (.inl i.val))
      (fun a => (forecastCongruenceOutput (R := ℤ) inactive u label a : ZMod q)) =
      fun j i => (label j i : ZMod q) := by
  funext j i
  cases i with
  | inl i =>
    simp only [forecastNativeCoordinateResidue, Sum.elim_inl, forecastNativeSheetResidue]
    split <;> rfl
  | inr e => rfl

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem forecastNativeDeckResidueMatrix_apply (q : ℕ) [NeZero q] (j : Fin m)
    (label : Fin (n j) ⊕ E j → ℤ) :
    integerResidueMatrix (forecastNativeDeckResidueMatrix U b hb bW q j) q *ᵥ
        integerResidueMap _ q label =
      integerResidueMap _ q
        ((standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm label) :=
  ((Classical.choose_spec (exists_bounded_integerMap_residue_matrix
    (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm.toLinearMap q)).2 label).symm

theorem forecastNativeAmbientDeckResidue_output (q : ℕ) [NeZero q]
    (u : X → ℤ) (sheet : ∀ j, Fin (n j) → ℤ) (deck : ∀ j, E j → ℤ) :
    forecastNativeAmbientDeckResidue inactive U b hb bW q (fun j i => sheet j i.val)
      (fun a => (forecastCongruenceOutput (R := ℤ) inactive u (fun j => Sum.elim (sheet j) (deck j)) a : ZMod q)) =
      fun a : Σ j, J j =>
        (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
          (sheet a.1) (deck a.1) a.2 : ZMod q) := by
  unfold forecastNativeAmbientDeckResidue
  have hcoord := forecastNativeCoordinateResidue_output inactive q u
    (fun j => Sum.elim (sheet j) (deck j))
  simp only [Sum.elim_inl] at hcoord
  simp only [hcoord]
  funext a
  exact congrFun (forecastNativeDeckResidueMatrix_apply U b hb bW q a.1
    (Sum.elim (sheet a.1) (deck a.1))) a.2

theorem forecastNativeAmbientDeckResidue_reduction (q : ℕ) [NeZero q]
    {d : ℕ} (hd : d ∣ q) (u : X → ℤ)
    (sheet : ∀ j, Fin (n j) → ℤ) (deck : ∀ j, E j → ℤ) :
    zmodPiReduction hd
      (forecastNativeAmbientDeckResidue inactive U b hb bW q (fun j i => sheet j i.val)
        (fun a => (forecastCongruenceOutput (R := ℤ) inactive u
          (fun j => Sum.elim (sheet j) (deck j)) a : ZMod q))) =
      fun a : Σ j, J j =>
        (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
          (sheet a.1) (deck a.1) a.2 : ZMod d) := by
  rw [forecastNativeAmbientDeckResidue_output]
  funext a
  exact map_intCast (ZMod.castHom hd (ZMod d)) _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastRawSpatialBoxReorder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

attribute [local instance] OAI.Erdos3.VectorPolynomial.instDecidableEqUnit
private theorem uniform_complex_integral {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℂ) :
    (∫ a, f a ∂(PMF.uniformOfFintype α).toMeasure) = 𝔼 a, f a := by
  rw [PMF.integral_eq_sum, Fintype.expect_eq_sum_div_card]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, ← Finset.mul_sum]
  rw [div_eq_inv_mul]

variable {m : ℕ} (E : Fin m → Type*) (N : ℕ)

theorem forecastSingleDeckAverage [∀ j, Fintype (E j)] [NeZero N]
    (f : ForecastSingleDeckResidues E N → ℂ) :
    (∫ deck, f deck ∂mixedCoveredJetDeckReference (fun _ : Fin m => Unit) E N) =
      𝔼 r : (Σ j, E j) → ZMod N, f (fun j _ e => r ⟨j, e⟩) := by
  rw [mixedCoveredJetDeckReference, uniform_complex_integral]
  exact Fintype.expect_equiv (forecastSingleDeckEquiv E N) f
    (fun r => f (fun j _ e => r ⟨j, e⟩)) (fun deck => by congr 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)

omit [∀ j, Fintype (I j)] in
theorem forecastShortGridSheet_of_mixed
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastShortGridSheet (I := I) U b Lsize (fun a _ => (w a.val.1).2 a.val.2) =
      fun j i => (w j).2 i.val := rfl

omit [∀ j, Fintype (I j)] in
theorem forecastShortGridNormalized_of_mixed (R : Fin m → ℝ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastShortGridNormalized U b Lsize R (fun a _ => (w a.val.1).2 a.val.2) =
      fun a => allocatedFullMixedSiteValue (R := R) U b w a.val := by
  funext a
  rcases a with ⟨⟨j, i⟩, ha⟩
  cases i with
  | inl i => exact False.elim ha
  | inr i => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

private theorem real_divisor_nsmul_circle (N d : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hdiv : d ∣ N) (a : ℝ) :
    (N / d) • ((a / N : ℝ) : UnitAddCircle) = ((a / d : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ((N / d : ℕ) : ℝ) * d = N := by exact_mod_cast Nat.div_mul_cancel hdiv
  rw [← mul_div_assoc]
  apply (div_eq_div_iff hn hd0).mpr
  calc
    ((N / d : ℕ) : ℝ) * a * d = a * (((N / d : ℕ) : ℝ) * d) := by ring
    _ = a * N := by rw [he]

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem forecastNativeCoveredChart_commonCover_ambient
    (N d : ℕ) [NeZero N] (hd : 0 < d) (hdiv : d ∣ N)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ)
    (a : Σ j, J j) :
    coveredJetAmbientTorus U (N / d)
      (fun j (_ : Unit) => normalizedCoveredChart (euclideanSubspace (U j))
        (basis j) (hb j) (bW j) N
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) N (deck j)))
      ⟨a.1, (), a.2⟩ =
      (((normalizedLatticePoint (euclideanSubspace (U a.1)) (basis a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 +
          (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (basis a.1) (hb a.1)
            (w a.1).2 (deck a.1) a.2 : ℝ)) / d : ℝ) : UnitAddCircle) := by
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    ((N / d) • normalizedCoveredChart (euclideanSubspace (U a.1)) (basis a.1) (hb a.1)
      (bW a.1) N (orthonormalMixedChart (o a.1) (w a.1), integerResidueMap (E a.1) N (deck a.1)))) a.2 = _
  rw [map_nsmul, map_nsmul, Pi.smul_apply,
    forecastNativeCoveredChart_ambient U basis o hb bW N w deck a]
  exact real_divisor_nsmul_circle N d (Nat.pos_of_ne_zero (NeZero.ne N)) hd hdiv _

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

theorem nativeSingleSiteCoverObservable_mixed_eq_forecastShortGridTest
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (Lsize : ℕ) (R : Fin m → ℝ) (hR : ∀ j, R j ≠ 0)
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (base u : X → ℤ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {τ : ℝ} (hτ : τ ≠ 0) (N : ℕ) [NeZero N] (hWN : W.cover ∣ N)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ) :
    nativeSingleSiteCoverObservable U W physicalN u N
      (fun j (_ : Unit) => normalizedCoveredChart (euclideanSubspace (U j))
        (basis j) (hb j) (bW j) N
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) N (deck j))) =
    W.forecastShortGridTest U basis Lsize hb o bW R q hm hperiod hcover
      (fun x => (base x : ℝ) / physicalN x) τ
      (fun a _ => (w a.val.1).2 a.val.2)
      (fun output => (forecastCongruenceOutput (R := ℤ)
        (allocatedShortAxis (I := I) U basis Lsize) u
          (fun j => Sum.elim (w j).2 (deck j)) output : ZMod q))
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        fun a => allocatedFullMixedSiteValue (R := R) U basis w a.1.val) := by
  unfold forecastShortGridTest forecastResidueTest
  rw [forecastShortGridSheet_of_mixed, forecastShortGridNormalized_of_mixed,
    forecastNativeSpatialResidue_reduction, forecastNativeAmbientDeckResidue_reduction,
    W.forecastPullback_mixed U basis o R _ hR base u physicalN hN hτ]
  simp only [nativeSingleSiteCoverObservable, frozenTorus]
  congr 2
  apply Prod.ext
  · rfl
  · funext a
    exact forecastNativeCoveredChart_commonCover_ambient U basis hb o bW N W.cover
      W.cover_pos hWN w deck a

theorem nativeSingleSiteCoverObservable_normalized_raw_point
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (Lsize : ℕ) (R : Fin m → ℝ) (hR : ∀ j, R j ≠ 0)
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (base u : X → ℤ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {τ : ℝ} (hτ : τ ≠ 0) (N : ℕ) [NeZero N] (hWN : W.cover ∣ N)
    (v : (Σ j, I j) → ℝ)
    (ks : AllocatedShortIntegerAxis U basis Lsize → ℤ)
    (ka : AllocatedActiveIntegerAxis U basis Lsize → ℤ)
    (deck : ForecastSingleDeckResidues E N) :
    nativeSingleSiteCoverObservable U W physicalN u N
      (mixedCoveredJetChart U o basis hb bW N
        (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
          (forecastIntegerAxisMerge U basis Lsize ks ka) deck)) =
      W.forecastShortGridTest U basis Lsize hb o bW R q hm hperiod hcover
        (fun x => (base x : ℝ) / physicalN x) τ (fun a _ => ks a)
        (forecastJointNativeResidue (I := I) U basis Lsize
          (fun j e => (((deck j () e).val : ℤ) : ZMod q))
          (Sum.elim (fun x => (u x : ZMod q)) (fun a => (ka a : ZMod q))))
        ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
          forecastActiveCoordinateJoin U basis Lsize v
            (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R Lsize a)) := by
  let w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun j => (fun i => R j * v ⟨j, i⟩,
      fun i => forecastIntegerAxisMerge U basis Lsize ks ka ⟨j, i⟩)
  let deckInt : ∀ j, E j → ℤ := fun j e => ((deck j () e).val : ℤ)
  have hchart : mixedCoveredJetChart U o basis hb bW N
      (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis Lsize ks ka) deck) =
      fun j (_ : Unit) => normalizedCoveredChart (euclideanSubspace (U j))
        (basis j) (hb j) (bW j) N
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) N (deckInt j)) := by
    funext j t
    cases t
    change normalizedCoveredChart _ _ _ _ _ (_, deck j ()) = _
    congr 1
    apply Prod.ext
    · rfl
    · funext e
      change deck j () e = (((deck j () e).val : ℤ) : ZMod N)
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hgrid : (fun a : AllocatedShortIntegerAxis U basis Lsize =>
      fun _ : (Finset.univ : Finset (Finset Empty)) => (w a.val.1).2 a.val.2) =
      (fun a _ => ks a) := by
    funext a t
    exact forecastIntegerAxisMerge_short U basis Lsize ks ka a
  have hcoord : (fun a => allocatedFullMixedSiteValue (R := R) U basis w a.1.val) =
      forecastActiveCoordinateJoin U basis Lsize v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R Lsize a) := by
    change forecastNormalizedActiveCoordinates (allocatedShortAxis (I := I) U basis Lsize)
      (allocatedFullMixedSiteValue (R := R) U basis w) = _
    rw [forecastActiveCoordinateJoin_mixed]
    congr 1
    · funext a
      exact mul_div_cancel_left₀ (v a) (hR a.1)
    · funext a
      change ((forecastIntegerAxisMerge U basis Lsize ks ka a.val : ℤ) : ℝ) / _ = _
      rw [forecastIntegerAxisMerge_active]
  rw [hchart, W.nativeSingleSiteCoverObservable_mixed_eq_forecastShortGridTest
    U basis hb o bW Lsize R hR q hm hperiod hcover base u physicalN hN hτ N hWN w deckInt,
    hgrid, hcoord, forecastJointNativeResidue_integer]

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

theorem forecastJointOriginalGridMean_mul_normalization
    (hV : gridVolume ≠ 0) (hscale : ∀ j, scale j ≠ 0) :
    (gridVolume : ℂ) * ((∏ j, scale j : ℝ) : ℂ) *
      forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
        gridVolume density test center scale =
    𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
      ∑' z, ∑' k : Joint → ℤ,
        (density (join c (fun j => ((k j : ℝ) - center j) / scale j)) : ℂ) *
        (rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axis a)) : ℂ) *
        test z (fun a => Sum.elim (zmodPiReduction hq aux)
          (fun j => (k j : ZMod q)) (axis a))
          (join c (fun j => ((k j : ℝ) - center j) / scale j)) := by
  have hVc : (gridVolume : ℂ) ≠ 0 := by exact_mod_cast hV
  have hTc : ((∏ j, scale j : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun j _ => hscale j)
  unfold forecastJointOriginalGridMean
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro aux haux
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ (fun c => ?_)
  dsimp only
  rw [mul_assoc, mul_div_cancel₀ _ hTc]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  push_cast
  field_simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastShortGridEquiv
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem forecastShortGrid_tsum {A : Type*}
    (f : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) → ℂ) :
    (∑' k : A → ℤ, f (fun a _ => k a)) = ∑' grid, f grid :=
  (forecastShortGridEquiv A).tsum_eq f

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastOriginalNativeHaarJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*}
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem forecastJointNativeResidue_eq_axis [Fintype X]
    [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] (L : ℕ) (hm : 0 < m) {A : Type*}
    (deck : ∀ j, E j → A) (r : X ⊕ AllocatedActiveIntegerAxis U basis L → A) :
    forecastJointNativeResidue (I := I) U basis L deck r =
      fun a => Sum.elim (fun a : Σ j, E j => deck a.1 a.2) r
        (forecastCongruenceJointAxisEquiv (I := I) U basis L hm a) := by
  funext a
  rcases a with ⟨j, x | e | i⟩ <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

theorem forecastLawDensityPhysicalChartSource_normalized_raw_point
    (hR : ∀ j, 0 < R j)
    (hselected : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (u : X → ℤ) (v : (Σ j, I j) → ℝ)
    (ks : AllocatedShortIntegerAxis U basis S.value → ℤ)
    (ka : AllocatedActiveIntegerAxis U basis S.value → ℤ)
    (deck : ForecastSingleDeckResidues Eout N) :
    forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
      active Y N volume base physicalN τ u
      (forecastSingleMixedRawPoint I Eout n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis S.value ks ka) deck) =
    (density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastActiveCoordinateJoin U basis S.value v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a)) : ℂ) *
    (rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => ks ⟨selected a, hselected a⟩)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
          (fun i => ((deck j () i).val : ℤ))) output : ZMod N)) : ℂ) := by
  let w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun j => (fun i => R j * v ⟨j, i⟩,
      fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
  have hactive : forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis w) =
      forecastActiveCoordinateJoin U basis S.value v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a) := by
    rw [forecastActiveCoordinateJoin_mixed]
    congr 1
    · funext a
      change R a.1 * v a / R a.1 = v a
      exact mul_div_cancel_left₀ (v a) (hR a.1).ne'
    · funext a
      change ((forecastIntegerAxisMerge U basis S.value ks ka a.val : ℤ) : ℝ) / _ = _
      rw [forecastIntegerAxisMerge_active]
  have hgrid : (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
      forecastIntegerAxisMerge U basis S.value ks ka (selected a)) =
      (fun a (_ : (Finset.univ : Finset (Finset Empty))) => ks ⟨selected a, hselected a⟩) := by
    funext a t
    exact forecastIntegerAxisMerge_short U basis S.value ks ka ⟨selected a, hselected a⟩
  change (density (_, forecastNormalizedActiveCoordinates short
    (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) * _ = _
  rw [hactive]
  congr 2
  congr 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

private theorem zmodReduction_val_p0 {N q : ℕ} [NeZero N] (hq : q ∣ N) (r : ZMod N) :
    (((r.val : ℤ) : ZMod q)) = ZMod.castHom hq (ZMod q) r := by
  rw [Int.cast_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val r]
  rw [map_natCast]

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Short" => AllocatedShortIntegerAxis U basis S.value
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

 theorem forecastLawNativeJointRawIntegrand
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : τ ≠ 0)
    (v : (Σ j, I j) → ℝ) (ks : Short → ℤ)
    (k : X ⊕ IntAxis → ℤ) (deck : ForecastSingleDeckResidues E N) :
    let u : X → ℤ := fun x => k (.inl x)
    let ka : IntAxis → ℤ := fun a => k (.inr a)
    let z := forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
      (forecastIntegerAxisMerge U basis S.value ks ka) deck
    let y := forecastJointCoordinateJoin U basis S.value v
      (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
        forecastJointGridScale U basis R S.value physicalN τ j)
    let axisIndex := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
    forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
      active Y N gridVolume base physicalN τ u z *
        nativeSingleSiteCoverObservable U W physicalN u N
          (mixedCoveredJetChart U o basis hb bW N z) =
      (density y : ℂ) *
      (rationalInactiveForecast law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        Y N gridVolume (fun a _ => ks a)
        (fun a => Sum.elim (fun e : Σ j, E j => deck e.1 () e.2)
          (fun j => (k j : ZMod N)) (axisIndex a)) : ℂ) *
      W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
        (fun x => (base x : ℝ) / physicalN x) τ (fun a _ => ks a)
        (fun a => Sum.elim (zmodPiReduction hq (fun e : Σ j, E j => deck e.1 () e.2))
          (fun j => (k j : ZMod q)) (axisIndex a)) y := by
  dsimp only
  let u : X → ℤ := fun x => k (.inl x)
  let ka : IntAxis → ℤ := fun a => k (.inr a)
  have hk : Sum.elim u ka = k := by funext a; cases a <;> rfl
  have hy : forecastJointCoordinateJoin U basis S.value v
      (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
        forecastJointGridScale U basis R S.value physicalN τ j) =
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastActiveCoordinateJoin U basis S.value v
          (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a)) := by
    rw [← hk, forecastJointGrid_normalized_join]
    rfl
  rw [hy, forecastLawDensityPhysicalChartSource_normalized_raw_point B U basis S law density selected
    sample x active Y N gridVolume base physicalN τ hR (fun a => a.property)]
  rw [W.nativeSingleSiteCoverObservable_normalized_raw_point U basis hb o bW S.value R
    (fun j => (hR j).ne') q hm hperiod hcover base u physicalN hN hτ N
    (dvd_trans hcover hq)]
  have hres (p : ℕ) :
      (fun a => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
          (fun i => ((deck j () i).val : ℤ))) a : ZMod p)) =
      fun a => Sum.elim (fun e : Σ j, E j => (((deck e.1 () e.2).val : ℤ) : ZMod p))
        (fun j => (k j : ZMod p))
        (forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm a) := by
    rw [← forecastJointNativeResidue_integer, forecastJointNativeResidue_eq_axis U basis _ hm]
    funext a
    rcases a with ⟨j, x | e | i⟩ <;> rfl
  rw [hres, forecastJointNativeResidue_eq_axis U basis _ hm]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  congr 2
  funext a
  rcases a with ⟨j, a | e | i⟩
  · rfl
  · change ((deck j () e).val : ZMod q) = ZMod.castHom hq (ZMod q) (deck j () e)
    simpa only [Int.cast_natCast] using zmodReduction_val_p0 hq (deck j () e)
  · rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "Short" => AllocatedShortIntegerAxis U basis S.value
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "raw" => mixedCoveredJetRawReference (I := I) (O := fun _ : Fin m => Unit) (E := E) (n := n) N
local notation "source" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x active Y N gridVolume base physicalN τ
local notation "chart" => mixedCoveredJetChart (O := fun _ : Fin m => Unit) U o basis hb bW N

private theorem forecastLawNativeJointSum
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : τ ≠ 0)
    (aux : (Σ j, E j) → ZMod N) (v : (Σ j, I j) → ℝ) :
    (∑' ks : Short → ℤ, ∑' k : X ⊕ IntAxis → ℤ,
      let u := fun x => k (.inl x)
      let z := forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis S.value ks (fun a => k (.inr a)))
        (fun j _ e => aux ⟨j, e⟩)
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)) =
    ∑' grid : Short → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ,
    ∑' k : X ⊕ IntAxis → ℤ,
      let y := forecastJointCoordinateJoin U basis S.value v
        (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
          forecastJointGridScale U basis R S.value physicalN τ j)
      let axisIndex := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
      (density y : ℂ) *
        (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N gridVolume grid (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axisIndex a)) : ℂ) *
        W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun x => (base x : ℝ) / physicalN x) τ grid
          (fun a => Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)) (axisIndex a)) y
 := by
  let f := fun (grid : Short → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) =>
    ∑' k : X ⊕ IntAxis → ℤ,
      let y := forecastJointCoordinateJoin U basis S.value v
        (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
          forecastJointGridScale U basis R S.value physicalN τ j)
      let axisIndex := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
      (density y : ℂ) *
        (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N gridVolume grid (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axisIndex a)) : ℂ) *
        W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun x => (base x : ℝ) / physicalN x) τ grid
          (fun a => Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)) (axisIndex a)) y
  calc
    _ = ∑' ks : Short → ℤ, f (fun a _ => ks a) := by
      apply tsum_congr
      intro ks
      apply tsum_congr
      intro k
      exact forecastLawNativeJointRawIntegrand U basis B S law density sample x active Y N gridVolume
        base physicalN τ hb o bW W hR q hq hm hperiod hcover hN hτ v ks k
          (fun j _ e => aux ⟨j, e⟩)
    _ = ∑' grid, f grid := forecastShortGrid_tsum f

theorem forecastLawNativeRawSum_eq_jointMean_s2_oai
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : 0 < τ) (hV : gridVolume ≠ 0)
    (hf : ∀ u ∈ integerBox physicalN,
      Integrable (fun z => source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)) raw)
    (hzero : ∀ u ∉ integerBox physicalN, ∀ z,
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z) = 0) :
    (∑ u ∈ integerBox physicalN, ∫ z,
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z) ∂raw) =
    ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) *
      ((gridVolume : ℂ) * ((∏ j, forecastJointGridScale U basis R S.value physicalN τ j : ℝ) : ℂ) *
        forecastJointOriginalGridMean U basis S.value hm law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N q hq gridVolume density
          (W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun x => (base x : ℝ) / physicalN x) τ)
          (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
          (forecastJointGridScale U basis R S.value physicalN τ)) := by
  rw [forecastRawSpatialBox_normalized_integral_s2 I E N U basis S.value X R hR _ _ hf hzero]
  congr 1
  rw [forecastSingleDeckAverage E N]
  rw [forecastJointOriginalGridMean_mul_normalization U basis S.value hm law active _ Y N q hq
    gridVolume density _ _ _ hV
    (fun j => (forecastJointGridScale_pos U basis hR S.value physicalN hN hτ j).ne')]
  apply Finset.expect_congr rfl
  intro aux haux
  apply integral_congr_ae
  refine ae_of_all _ (fun v => ?_)
  exact forecastLawNativeJointSum U basis B S law density sample x active Y N gridVolume
    base physicalN τ hb o bW W hR q hq hm hperiod hcover hN hτ.ne' aux v

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.forecastLawNativeRawSum_eq_jointMean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.forecastLawNativeRawSum_eq_jointMean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
