-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_forecast_buffered_normalized_twist_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:33:03.330699+00:00
-- url     : https://prove2.me/submissions/84a6539c-46a5-4117-8bc9-51554798aea9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedBufferedTorusCutoff_eq_siteChart_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

theorem restrictedComplexChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedComplexChartDensity q S c f (q x) = (c : ℂ) * f x := by
  have he : Function.Injective (fun x : S => q x.val) := fun a b h => Subtype.ext (hinj a.property b.property h)
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (he.extend_apply (fun x => f x.val) (fun _ => 0) ⟨x, hx⟩)

theorem restrictedComplexChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) {y : Y} (hy : y ∉ q '' S) :
    restrictedComplexChartDensity q S c f y = 0 := by
  have hy' : y ∉ Set.range (fun x : S => q x.val) := by
    rintro ⟨x, rfl⟩
    exact hy ⟨x.val, x.property, rfl⟩
  simp only [restrictedComplexChartDensity, Function.extend_apply' _ _ _ hy', mul_zero]

end Erdos3

end

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealPoint_coordinates (x : EuclideanSpace ℝ D) :
    mixedRealPoint W b o (mixedRealCoordinates W b o x) = x := by
  change (normalizedOrthogonalChart W b).symm
    ((orthonormalChart o) ((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1),
      ((normalizedOrthogonalChart W b) x).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelLiftChart
namespace OAI

section

namespace Erdos3

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) (s : X → G) (q : X → H)

theorem kernelLiftChart_injOn (hproj : ∀ x, C (s x) = q x)
    {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × C.ker => s p.1 + p.2.val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  change s x.1 + x.2.val = s y.1 + y.2.val at he
  have hkx : C x.2.val = 0 := x.2.property
  have hky : C y.2.val = 0 := y.2.property
  have hb : q x.1 = q y.1 := by
    have ht := congrArg C he
    simpa only [map_add, hproj, hkx, hky, add_zero] using ht
  have hxy : x.1 = y.1 := hq hx.1 hy.1 hb
  apply Prod.ext hxy
  apply Subtype.ext
  rw [hxy] at he
  exact add_left_cancel he

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_injOn
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) :=
  kernelLiftChart_relabel_injOn _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)))
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SeparatedChartExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_complex_extension_of_distance_bound
    {A Y : Type*} [PseudoMetricSpace Y] (embed : A → Y) (f : A → ℂ) (L B : ℝ≥0)
    (hf : ∀ a b, dist (f a) (f b) ≤ L * dist (embed a) (embed b))
    (hb : ∀ a, ‖f a‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * L) g ∧ (∀ a, g (embed a) = f a) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  classical
  let S := Set.range embed
  let pre (y : S) : A := Classical.choose y.property
  have hpre (y : S) : embed (pre y) = y.val := Classical.choose_spec y.property
  have hF : LipschitzWith L (fun y : S => f (pre y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have h := hf (pre y) (pre z)
    rw [hpre y, hpre z] at h
    exact h
  obtain ⟨g, hg, heq, hgb⟩ := exists_complex_extension_from_subset S
    (fun y => f (pre y)) L B hF (fun y => hb (pre y))
  refine ⟨g, hg, ?_, hgb⟩
  intro a
  let y : S := ⟨embed a, ⟨a, rfl⟩⟩
  have hzero : dist (f (pre y)) (f a) ≤ 0 := by
    have h := hf (pre y) a
    rw [hpre y] at h
    simpa only [y, dist_self, mul_zero] using h
  exact (heq y).trans (dist_le_zero.mp hzero)

theorem exists_bounded_extension_on_separated_charts
    {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (chart : A → X → Y) (S : Set X) (K D L B : ℝ≥0)
    (hwithin : ∀ a x, x ∈ S → ∀ y, y ∈ S → dist x y ≤ K * dist (chart a x) (chart a y))
    (hsep : ∀ a b, a ≠ b → ∀ x, x ∈ S → ∀ y, y ∈ S →
      (1 : ℝ) ≤ D * dist (chart a x) (chart b y))
    (f : A → X → ℂ) (hf : ∀ a, LipschitzOnWith L (f a) S)
    (hb : ∀ a x, x ∈ S → ‖f a x‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * max (L * K) (2 * B * D)) g ∧
      (∀ a x, x ∈ S → g (chart a x) = f a x) ∧ ∀ y, ‖g y‖ ≤ 2 * B := by
  let P := {p : A × X // p.2 ∈ S}
  let embed : P → Y := fun p => chart p.val.1 p.val.2
  let F : P → ℂ := fun p => f p.val.1 p.val.2
  let C := max (L * K) (2 * B * D)
  have hLC : ((L * K : ℝ≥0) : ℝ) ≤ C := by exact_mod_cast le_max_left (L * K) (2 * B * D)
  have hDC : ((2 * B * D : ℝ≥0) : ℝ) ≤ C := by exact_mod_cast le_max_right (L * K) (2 * B * D)
  have hF (p q : P) : dist (F p) (F q) ≤ C * dist (embed p) (embed q) := by
    rcases p with ⟨⟨a, x⟩, hx⟩
    rcases q with ⟨⟨b, y⟩, hy⟩
    change dist (f a x) (f b y) ≤ C * dist (chart a x) (chart b y)
    by_cases hab : a = b
    · subst b
      calc
        _ ≤ (L : ℝ) * dist x y := (hf a).dist_le_mul x hx y hy
        _ ≤ (L : ℝ) * (K * dist (chart a x) (chart a y)) :=
          mul_le_mul_of_nonneg_left (hwithin a x hx y hy) L.coe_nonneg
        _ = ((L * K : ℝ≥0) : ℝ) * dist (chart a x) (chart a y) := by
          rw [NNReal.coe_mul, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right hLC dist_nonneg
    · have hs := hsep a b hab x hx y hy
      have hn : dist (f a x) (f b y) ≤ 2 * (B : ℝ) := by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (by linarith [hb a x hx, hb b y hy])
      calc
        _ ≤ 2 * (B : ℝ) := hn
        _ ≤ (2 * (B : ℝ)) * (D * dist (chart a x) (chart b y)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * (B : ℝ))
        _ = ((2 * B * D : ℝ≥0) : ℝ) * dist (chart a x) (chart b y) := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDC dist_nonneg
  obtain ⟨g, hg, heq, hgb⟩ := exists_complex_extension_of_distance_bound embed F C B hF
    (fun p => hb p.val.1 p.val.2 p.property)
  exact ⟨g, hg, fun a x hx => heq ⟨(a, x), hx⟩, hgb⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable (q : ℕ) [NeZero q]

theorem circleQuarterCover_zero (a : ZMod q) :
    circleQuarterCover q a 0 = ZMod.toAddCircle a := by
  simp only [circleQuarterCover, zero_div, AddCircle.coe_zero, add_zero]

theorem circleQuarterCover_dist (a : ZMod q) {x y : ℝ}
    (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (q : ℝ) * dist (circleQuarterCover q a x) (circleQuarterCover q a y) = dist x y := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxy : |x - y| ≤ 1 / 2 := by
    have htri : |x - y| ≤ |x| + |y| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
    linarith
  have hsmall : |(x - y) / q| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (hxy.trans (by linarith))
  have hn : ‖(((x - y) / q : ℝ) : UnitAddCircle)‖ = |(x - y) / q| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hsmall)
  unfold circleQuarterCover
  rw [dist_add_left, dist_eq_norm, ← AddCircle.coe_sub, ← sub_div, hn,
    abs_div, abs_of_pos hq, mul_div_cancel₀ _ hq.ne', Real.dist_eq]

theorem circleQuarterCover_center_dist (a : ZMod q) {x : ℝ} (hx : |x| ≤ 1 / 4) :
    (q : ℝ) * dist (circleQuarterCover q a x) (ZMod.toAddCircle a) ≤ 1 / 4 := by
  have h := circleQuarterCover_dist q a hx (by norm_num : |(0 : ℝ)| ≤ 1 / 4)
  rw [circleQuarterCover_zero, Real.dist_eq, sub_zero] at h
  exact h.le.trans hx

theorem circleQuarterCover_separated {a b : ZMod q} (hab : a ≠ b) {x y : ℝ}
    (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (1 : ℝ) ≤ (2 * q) * dist (circleQuarterCover q a x) (circleQuarterCover q b y) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha := circleQuarterCover_center_dist q a hx
  have hb := circleQuarterCover_center_dist q b hy
  rw [dist_comm] at ha
  have ht : dist (ZMod.toAddCircle a) (ZMod.toAddCircle b) ≤
      dist (ZMod.toAddCircle a) (circleQuarterCover q a x) +
        dist (circleQuarterCover q a x) (circleQuarterCover q b y) +
          dist (circleQuarterCover q b y) (ZMod.toAddCircle b) := by
    linarith [dist_triangle (ZMod.toAddCircle a) (circleQuarterCover q a x) (ZMod.toAddCircle b),
      dist_triangle (circleQuarterCover q a x) (circleQuarterCover q b y) (ZMod.toAddCircle b)]
  have hs := CircleFourier.one_le_mul_dist_toAddCircle hab
  have hm := mul_le_mul_of_nonneg_left ht hq
  nlinarith

theorem quarterCoverPoint_intCast {D : Type*} (a : D → ℤ) (x : D → ℝ) :
    quarterCoverPoint q (fun i => (a i : ZMod q)) x =
      fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle) := by
  funext i
  change ZMod.toAddCircle (a i : ZMod q) + ((x i / q : ℝ) : UnitAddCircle) = _
  rw [ZMod.toAddCircle_intCast, ← AddCircle.coe_add, ← add_div]

theorem quarterCoverPoint_within {D : Type*} [Fintype D] (a : D → ZMod q) {x y : D → ℝ}
    (hx : ∀ i, |x i| ≤ 1 / 4) (hy : ∀ i, |y i| ≤ 1 / 4) :
    dist x y ≤ (q : ℝ) * dist (quarterCoverPoint q a x) (quarterCoverPoint q a y) := by
  apply (dist_pi_le_iff (mul_nonneg (Nat.cast_nonneg q) dist_nonneg)).mpr
  intro i
  calc
    dist (x i) (y i) = (q : ℝ) * dist (circleQuarterCover q (a i) (x i))
        (circleQuarterCover q (a i) (y i)) := (circleQuarterCover_dist q (a i) (hx i) (hy i)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dist_le_pi_dist (quarterCoverPoint q a x) (quarterCoverPoint q a y) i) (Nat.cast_nonneg q)

theorem quarterCoverPoint_separated {D : Type*} [Fintype D] {a b : D → ZMod q} (hab : a ≠ b)
    {x y : D → ℝ} (hx : ∀ i, |x i| ≤ 1 / 4) (hy : ∀ i, |y i| ≤ 1 / 4) :
    (1 : ℝ) ≤ (2 * q) * dist (quarterCoverPoint q a x) (quarterCoverPoint q b y) := by
  obtain ⟨i, hi⟩ := not_forall.mp (fun h : ∀ i, a i = b i => hab (funext h))
  exact (circleQuarterCover_separated q hi (hx i) (hy i)).trans
    (mul_le_mul_of_nonneg_left
      (dist_le_pi_dist (quarterCoverPoint q a x) (quarterCoverPoint q b y) i) (by positivity))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_parametric_quarter_cover_extension
    {Y D : Type*} [PseudoMetricSpace Y] [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → Y × (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : Y × (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧
      (∀ a y x, (∀ i, |x i| ≤ 1 / 4) → g (y, quarterCoverPoint q a x) = f a (y, x)) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  let chart : (D → ZMod q) → Y × (D → ℝ) → Y × (D → UnitAddCircle) :=
    fun a p => (p.1, quarterCoverPoint q a p.2)
  let Q : Set (Y × (D → ℝ)) := {p | ∀ i, |p.2 i| ≤ 1 / 4}
  have hwithin (a : D → ZMod q) (x : Y × (D → ℝ)) (hx : x ∈ Q)
      (y : Y × (D → ℝ)) (hy : y ∈ Q) :
      dist x y ≤ (max 1 (q : ℝ≥0) : ℝ) * dist (chart a x) (chart a y) := by
    have hK1 : (1 : ℝ) ≤ (max 1 (q : ℝ≥0) : ℝ) := by
      exact_mod_cast le_max_left (1 : ℝ≥0) (q : ℝ≥0)
    have hKq : (q : ℝ) ≤ (max 1 (q : ℝ≥0) : ℝ) := by
      exact_mod_cast le_max_right (1 : ℝ≥0) (q : ℝ≥0)
    change max (dist x.1 y.1) (dist x.2 y.2) ≤
      (max 1 (q : ℝ≥0) : ℝ) * max (dist x.1 y.1)
        (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q a y.2))
    apply max_le
    · calc
        dist x.1 y.1 ≤ max (dist x.1 y.1)
            (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q a y.2)) := le_max_left _ _
        _ = 1 * max (dist x.1 y.1)
            (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q a y.2)) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hK1 (le_trans dist_nonneg (le_max_left _ _))
    · exact (quarterCoverPoint_within q a hx hy).trans
        (mul_le_mul hKq (le_max_right _ _) dist_nonneg (by positivity))
  have hsep (a b : D → ZMod q) (hab : a ≠ b)
      (x : Y × (D → ℝ)) (hx : x ∈ Q) (y : Y × (D → ℝ)) (hy : y ∈ Q) :
      (1 : ℝ) ≤ (2 * (q : ℝ≥0) : ℝ≥0) * dist (chart a x) (chart b y) := by
    have h := quarterCoverPoint_separated q hab hx hy
    change (1 : ℝ) ≤ (2 * (q : ℝ)) * max (dist x.1 y.1)
      (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q b y.2))
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_bounded_extension_on_separated_charts
    chart Q (max 1 q) (2 * q) L B hwithin hsep f
    (fun a => (hf a).lipschitzOnWith) (fun a x _ => hb a x)
  refine ⟨g, ?_, fun a y x hx => hvalue a (y, x) hx, hbound⟩
  have heq : 2 * B * (2 * (q : ℝ≥0)) = 4 * B * q := by ring
  simpa only [heq] using hg

theorem exists_parametric_integer_quarter_cover_extension
    {Y D : Type*} [PseudoMetricSpace Y] [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → Y × (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : Y × (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧
      (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (a : D → ℤ) (y : Y) (x : D → ℝ), (∀ i, |x i| ≤ 1 / 4) →
        g (y, fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle)) =
          f (fun i => (a i : ZMod q)) (y, x) := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_parametric_quarter_cover_extension q f L B hf hb
  refine ⟨g, hg, hbound, ?_⟩
  intro a y x hx
  rw [← quarterCoverPoint_intCast]
  exact hvalue (fun i => (a i : ZMod q)) y x hx

end Erdos3

end

section

namespace Erdos3

open Module Submodule

theorem exists_covered_representative_offset
    {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (d : ℕ) [NeZero d] (u : W) (x : W × (Fin n → ℤ)) (r : E → ZMod d)
    (hu : (QuotientAddGroup.mk u : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW d (x, r)) :
    ∃ w : E → ℤ, normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val =
        (d : ℝ) • u ∧ integerResidueMap E d w = r := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (NeZero.pos d)
  have hp := congrArg (quotientIntegerCover Γ d) hu
  change quotientIntegerCover Γ d (QuotientAddGroup.mk' Γ u) =
    quotientIntegerCover Γ d (normalizedCoverLift W b hb d x + (e r).val) at hp
  rw [quotientIntegerCover_mk, map_add, (e r).property, add_zero,
    normalizedCoverLift_projection W b hb d (NeZero.pos d)] at hp
  obtain ⟨w, hw⟩ := exists_normalized_representative_offset W bW b hb ((d : ℝ) • u) x hp
  refine ⟨w, hw, ?_⟩
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have he := normalizedCoverLift_add_deck W bW b hb d (NeZero.pos d) x w
  rw [hw, smul_smul, inv_mul_cancel₀ hd0, one_smul] at he
  have hsum : normalizedCoverLift W b hb d x + (e (integerResidueMap E d w)).val =
      normalizedCoverLift W b hb d x + (e r).val := he.trans hu
  apply e.injective
  exact Subtype.ext (add_left_cancel hsum)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (mixedCoveredJetChart U o b hb bW d) (mixedCoveredJetRegion U o b d Ω) := by
  intro z hz w hw he
  apply (mixedCoveredJetCoordinatesEquiv U o d).injective
  exact coveredJetChart_injOn U b hb bW d Ω hΩ hz hw he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteAmbient
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) [NeZero d]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem physicalSingleSiteValue_ambient (w : X → ℝ) :
    coveredJetAmbientTorus U d (physicalSingleSiteValue U d p hm w) =
      fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
        ((eval w (p a.1)) a.2.2 : UnitAddCircle) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  funext a
  rcases a with ⟨j, t, i⟩
  cases t
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (d • (euclideanSubspaceTorusEquiv (U j)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
        (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j)))))) i = _
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  change subspaceAmbientTorus (U j) (quotientIntegerCover _ d
    (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
      (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))) i = _
  rw [quotientIntegerCover_mk, subspaceAmbientTorus_mk]
  simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [eval_restrictCoefficients]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoordinateCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem normalizedCoordinateCutoff_spec (D : Type*) [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) :
    ContDiff ℝ ∞ (normalizedCoordinateCutoff D r hr) ∧
      HasCompactSupport (normalizedCoordinateCutoff D r hr) ∧
      (∀ v, 0 ≤ normalizedCoordinateCutoff D r hr v ∧ normalizedCoordinateCutoff D r hr v ≤ 1) ∧
      (∀ v, (∀ d, |v d| ≤ (r : ℝ)) → normalizedCoordinateCutoff D r hr v = 1) ∧
      (∀ v, normalizedCoordinateCutoff D r hr v ≠ 0 → ∀ d, |v d| ≤ 2 * (r : ℝ)) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r))
        (normalizedCoordinateCutoff D r hr) :=
  Classical.choose_spec (exists_normalized_site_cutoff (D := D) r hr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

theorem allocatedFullAmbientSiteCoordinates_point
    (z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ)) :
    allocatedFullAmbientSiteCoordinates (R := R) U b o (mixedJetAmbientPoint U b o z) =
      allocatedFullMixedSiteValue (R := R) U b (fun j => mixedArrayRegroup _ _ _ (z j) ()) := by
  have hp (j : Fin m) : (EuclideanSpace.equiv (J j) ℝ).symm
      (fun k => mixedJetAmbientPoint U b o z ⟨j, (), k⟩) =
      normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) ())) := by
    have hv : (fun k => mixedJetAmbientPoint U b o z ⟨j, (), k⟩) =
        (EuclideanSpace.equiv (J j) ℝ) (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) ()))) := by
      funext k
      rfl
    rw [hv, ContinuousLinearEquiv.symm_apply_apply]
  funext a
  rcases a with ⟨j, i | i⟩ <;>
    dsimp only [allocatedFullAmbientSiteCoordinates, allocatedFullMixedSiteValue] <;>
    rw [hp, mixedRealCoordinates_integer] <;> rfl

theorem allocatedFullAmbientSiteCoordinates_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  let pz := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
  let pw := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => w ⟨a.1, (), k⟩))
  have hout : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤ dist pz pw := by
    rcases a.2 with i | i
    · exact (dist_le_pi_dist pz.1 pw.1 i).trans (le_max_left _ _)
    · exact (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
  have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U a.1)) (b a.1) (o a.1) (hC a.1)).comp
    (euclideanFromCoordinates_lipschitz (D := J a.1))).dist_le_mul
      (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩)
  have hin : dist (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨a.1, (), k⟩)
  have hc : C a.1 * Fintype.card (J a.1) ≤ ∑ j, C j * Fintype.card (J j) :=
    Finset.single_le_sum (f := fun j => C j * Fintype.card (J j))
      (fun _ _ => by positivity) (Finset.mem_univ a.1)
  have hd : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤
      ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w :=
    (hout.trans hrow).trans ((mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg))
  change |Sum.elim pz.1 pz.2 a.2 / R a.1 - Sum.elim pw.1 pw.2 a.2 / R a.1| ≤ _
  rw [← sub_div, abs_div, abs_of_pos (hR a.1)]
  calc
    _ ≤ (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) / R a.1 :=
      div_le_div_of_nonneg_right hd (hR a.1).le
    _ = (R a.1)⁻¹ * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) := by ring
    _ ≤ (K : ℝ) * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) :=
      mul_le_mul_of_nonneg_right (hK a.1) (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem singleSiteFromLayered_lipschitz : LipschitzWith 1 (singleSiteFromLayered (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  exact dist_le_pi_dist v w ⟨a.1, a.2.2⟩

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

theorem allocatedFullAmbientSiteCoordinates_layered_point
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    allocatedFullAmbientSiteCoordinates (R := R) U b o
      (singleSiteFromLayered (fun a : Σ j, J j =>
        normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1) (orthonormalMixedChart (o a.1) (w a.1)) a.2)) =
      allocatedFullMixedSiteValue (R := R) U b w := by
  let z := fun j => ((fun i (_ : Unit) => (w j).1 i), (fun i (_ : Unit) => (w j).2 i))
  change allocatedFullAmbientSiteCoordinates (R := R) U b o (mixedJetAmbientPoint U b o z) = _
  rw [allocatedFullAmbientSiteCoordinates_point]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedBufferedAmbientCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

theorem allocatedFullAmbientSiteCoordinates_norm_bound
    (hR : ∀ j, 0 < R j) (z : ambient → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ a, |allocatedFullAmbientSiteCoordinates (R := R) U b o z a| ≤ T)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖(EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (T * R j)) := by
  let v := (EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)
  let w := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j) v
  have hu (i : I j) : |w.1 i| ≤ T * R j := by
    have h := hz ⟨j, .inl i⟩
    change |w.1 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have hv (i : Fin (n j)) : |w.2 i| ≤ T * R j := by
    have h := hz ⟨j, .inr i⟩
    change |w.2 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have h := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg hT (hR j).le) (hchart j) w.1 w.2 hu hv
  dsimp only [w] at h
  rw [Prod.mk.eta, mixedRealPoint_coordinates] at h
  exact h

variable (r : ℝ≥0) (hr : 0 < r)

theorem allocatedBufferedAmbientCutoff_range (z : ambient → ℝ) :
    0 ≤ allocatedBufferedAmbientCutoff (R := R) U b o r hr z ∧
      allocatedBufferedAmbientCutoff (R := R) U b o r hr z ≤ 1 :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.1 _

theorem allocatedBufferedAmbientCutoff_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith ((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
      (K * ∑ j, C j * Fintype.card (J j)))
      (allocatedBufferedAmbientCutoff (R := R) U b o r hr) :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.2.2.comp
    (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR C hC K hK)

theorem allocatedBufferedAmbientCutoff_support (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (z : ambient → ℝ) (hz : allocatedBufferedAmbientCutoff (R := R) U b o r hr z ≠ 0) :
    ∀ a, |z a| ≤ 1 / 4 := by
  have hcoord := (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.2.1
    (allocatedFullAmbientSiteCoordinates (R := R) U b o z) hz
  rintro ⟨j, t, k⟩
  cases t
  have h := (allocatedFullAmbientSiteCoordinates_norm_bound U b o hR z (by positivity)
    hcoord C hC hchart j).trans (hbudget j)
  exact (PiLp.norm_apply_le ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)) k).trans h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalSiteProjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

omit [∀ j, Fintype (J j)] in
theorem physicalEuclideanSitePoint_apply (w : X → ℝ) (j : Fin m) (i : J j) :
    (physicalEuclideanSitePoint U p hm w j).val i = eval w (p j) i := by
  change (eval w (restrictCoefficients (U j) (p j) (hm j))).val i = _
  rw [eval_restrictCoefficients]

theorem physicalSingleSiteValue_eq_mk (d : ℕ) (w : X → ℝ) (j : Fin m) :
    physicalSingleSiteValue U d p hm w j () =
      QuotientAddGroup.mk ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j) := by
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  change euclideanSubspaceTorusEquiv (U j)
    ((euclideanSubspaceTorusEquiv (U j)).symm _) =
      euclideanSubspaceTorusEquiv (U j) (QuotientAddGroup.mk' _
        ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j))
  rw [AddEquiv.apply_symm_apply, euclideanSubspaceTorusEquiv_mk]
  congr 1

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ParametricFullResidueCoveredExtension
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical NNReal Matrix

theorem exists_normalized_full_residue_map
    {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (q : ℕ) [NeZero q] :
    ∃ r : (D → ZMod q) → (Fin n ⊕ E → ZMod q),
      ∀ (z : Fin n → ℤ) (w : E → ℤ),
        r (fun i => (latticeDeckInteger W bW b hb z w i : ZMod q)) =
          Sum.elim (fun i => (z i : ZMod q)) (fun i => (w i : ZMod q)) := by
  obtain ⟨A, _hA, hres⟩ := standardLatticeCoordinates_residue W bW b hb q
  refine ⟨fun a => integerResidueMatrix A q *ᵥ a, ?_⟩
  intro z w
  change integerResidueMatrix A q *ᵥ
    integerResidueMap D q (latticeDeckInteger W bW b hb z w) = _
  rw [← hres, latticeDeckInteger_coordinates]
  funext i
  cases i <;> rfl

end Erdos3

end

section

namespace Erdos3
open Module Submodule
open scoped Classical NNReal

theorem intCast_eq_residue_val_of_dvd {q d : ℕ} [NeZero d]
    (hqd : q ∣ d) (z : ℤ) (r : ZMod d) (hz : (z : ZMod d) = r) :
    (z : ZMod q) = (r.val : ZMod q) := by
  rw [← Int.cast_natCast]
  apply (ZMod.intCast_eq_intCast_iff z (r.val : ℤ) q).mpr
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hqd)
  apply (ZMod.intCast_eq_intCast_iff z (r.val : ℤ) d).mp
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hz

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Classical NNReal Matrix

theorem exists_parametric_layered_full_residue_extension
    {Y : Type*} [PseudoMetricSpace Y]
    {M : Type*} [Fintype M] {D E : M → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)] {n : M → ℕ}
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
    (q : ℕ) [NeZero q]
    (f : (∀ j, Fin (n j) ⊕ E j → ZMod q) → Y × ((Σ j, D j) → ℝ) → ℂ)
    (L B : ℝ≥0) (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a v, ‖f a v‖ ≤ B) :
    ∃ g : Y × ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (y : Y) (x : ∀ j, W j × (Fin (n j) → ℤ)) (w : ∀ j, E j → ℤ),
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (y, fun a => (((normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
          ((bW a.1).equivFun.symm (w a.1)).val).val a.2 / q : ℝ) : UnitAddCircle)) =
        f (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)))
          (y, fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  choose r hr using (fun j => exists_normalized_full_residue_map (W j) (bW j) (b j) (hb j) q)
  let label : ((Σ j, D j) → ZMod q) → (∀ j, Fin (n j) ⊕ E j → ZMod q) :=
    fun a j => r j (fun i => a ⟨j, i⟩)
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_parametric_integer_quarter_cover_extension q
    (fun a v => f (label a) v) L B (fun a => hf (label a)) (fun a v => hbound (label a) v)
  refine ⟨g, hg, hgb, ?_⟩
  intro y x w hx
  let β : (Σ j, D j) → ℤ := fun a =>
    latticeDeckInteger (W a.1) (bW a.1) (b a.1) (hb a.1) (x a.1).2 (w a.1) a.2
  let v : (Σ j, D j) → ℝ := fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2
  have hlabel : label (fun a => (β a : ZMod q)) =
      fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)) := by
    funext j
    exact hr j (x j).2 (w j)
  have h := hvalue β y v (fun a => hx a.1 a.2)
  rw [hlabel] at h
  have hpoint : (fun a => ((((β a : ℝ) + v a) / q : ℝ) : UnitAddCircle)) =
      fun a => (((normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
        ((bW a.1).equivFun.symm (w a.1)).val).val a.2 / q : ℝ) : UnitAddCircle) := by
    funext a
    have he := congrArg (fun z : EuclideanSpace ℝ (D a.1) => z a.2)
      (normalizedDeckPoint_identity (W a.1) (bW a.1) (b a.1) (hb a.1) (x a.1) (w a.1))
    change (normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
      ((bW a.1).equivFun.symm (w a.1)).val).val a.2 = v a + (β a : ℝ) at he
    rw [he, add_comm (β a : ℝ)]
  simpa only [hpoint] using h

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Classical NNReal

theorem exists_parametric_layered_full_residue_covered_extension
    {Y : Type*} [PseudoMetricSpace Y]
    {M : Type*} [Fintype M] {D E : M → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)] {n : M → ℕ}
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
    (q d : ℕ) [NeZero q] [NeZero d] (hqd : q ∣ d)
    (f : (∀ j, Fin (n j) ⊕ E j → ZMod q) → Y × ((Σ j, D j) → ℝ) → ℂ)
    (L B : ℝ≥0) (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a v, ‖f a v‖ ≤ B) :
    ∃ g : Y × ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (y : Y) (u : ∀ j, W j) (x : ∀ j, W j × (Fin (n j) → ℤ)) (r : ∀ j, E j → ZMod d),
        (∀ j, (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : W j ⧸
          (latticeSection (standardEuclideanLattice (D j)) (W j)).toAddSubgroup) =
            normalizedCoveredChart (W j) (b j) (hb j) (bW j) d (x j, r j)) →
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (y, fun a => (((u a.1).val a.2 / q : ℝ) : UnitAddCircle)) =
          f (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => ((r j i).val : ZMod q)))
            (y, fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_parametric_layered_full_residue_extension W bW b hb q f L B hf hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro y u x r hu hx
  choose w hw hr using (fun j =>
    exists_covered_representative_offset (W j) (bW j) (b j) (hb j) d
      ((d : ℝ)⁻¹ • u j) (x j) (r j) (hu j))
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at hw
  have he : (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q))) =
      (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => ((r j i).val : ZMod q))) := by
    funext j i
    cases i with
    | inl i => rfl
    | inr i => exact intCast_eq_residue_val_of_dvd hqd (w j i) (r j i) (congrFun (hr j) i)
  simpa only [hw, he] using hvalue y x w hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem lipschitz_complex_div_two {X : Type*} [PseudoMetricSpace X]
    (f : X → ℂ) (K : ℝ≥0) (hf : LipschitzWith (2 * K) f) :
    LipschitzWith K (fun x => f x / 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← sub_div, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := hf.dist_le_mul x y
  simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] at h
  nlinarith only [h]

theorem complex_div_two_norm_le {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖z / 2‖ ≤ 1 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_div, h2]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hz)

attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_range (x : ambient → UnitAddCircle) :
    0 ≤ allocatedBufferedTorusCutoff (R := R) U b o r hr x ∧
      allocatedBufferedTorusCutoff (R := R) U b o r hr x ≤ 1 := by
  apply smallBoxTorusKernel_range _ zero_le_one (allocatedBufferedAmbientCutoff_range U b o r hr)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_lipschitz
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith ((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
      (K * ∑ j, Cforward j * Fintype.card (J j))) (allocatedBufferedTorusCutoff (R := R) U b o r hr) := by
  apply smallBoxTorusKernel_lipschitz _
    (allocatedBufferedAmbientCutoff_lipschitz U b o r hr hR Cforward hforward K hK)
    (fun z => (allocatedBufferedAmbientCutoff_range U b o r hr z).1)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem forecastCoverCutoffInput_lipschitz (period : ℕ) :
    LipschitzWith (period : ℝ≥0) (forecastCoverCutoffInput (J := J) period) :=
  torus_nsmul_reindex_lipschitz
    (fun a : JetAmbientIndex (fun _ : Fin m => Unit) J => (⟨a.1, a.2.2⟩ : Σ j, J j)) period

omit [∀ j, Fintype (J j)] in
theorem forecastCoverCutoffInput_physicalGridFactorInput {X : Type*}
    (period : ℕ) [NeZero period]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    forecastCoverCutoffInput period (physicalGridFactorInput period p t) =
      fun a => (eval t (p a.1) a.2.2 : UnitAddCircle) := by
  have hp : (period : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne period)
  funext a
  simp only [forecastCoverCutoffInput, physicalGridFactorInput,
    ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  field_simp

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {Y : Type*} [PseudoMetricSpace Y]

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

omit [NeZero period] [PseudoMetricSpace Y] in
theorem forecastBufferedCoveredSiteFactor_on_chart
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) (w : MixedCoveredJetSource I single E n d) (hw : w ∈ region) :
    forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F s (chart w) =
      allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) (chart w) *
        F (forecastBufferedFullResidue d period w)
          (s, allocatedFullMixedSiteValue (R := R) U b
            (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [forecastBufferedCoveredSiteFactor, allocatedBufferedSiteChartFactor,
    restrictedComplexChartDensity_apply _ _ _ _ hinj hw, Complex.ofReal_one, one_mul]

omit [NeZero period] [PseudoMetricSpace Y] in
theorem forecastBufferedCoveredSiteFactor_zero_of_cutoff_zero
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) (y : EuclideanJetLayers U single)
    (hy : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y = 0) :
    forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F s y = 0 := by
  by_cases hmem : y ∈ chart '' region
  · obtain ⟨w, hw, rfl⟩ := hmem
    rw [forecastBufferedCoveredSiteFactor_on_chart B U b S o hb bW d r hr period F s w hw,
      hy, zero_mul]
  · unfold forecastBufferedCoveredSiteFactor
    exact restrictedComplexChartDensity_zero _ _ _ _ hmem

theorem exists_forecast_buffered_cover_factor
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hf : ∀ a, LipschitzWith L (F a)) (hf1 : ∀ a z, ‖F a z‖ ≤ 1) :
    ∃ g : Y × ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith
        (max ((L * max 1 (K * ∑ j, Cforward j * Fintype.card (J j))) *
          max 1 (period : ℝ≥0)) (4 * period)) g ∧
      (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ (s : Y) (u : ∀ j, euclideanSubspace (U j)) (y : EuclideanJetLayers U single),
        (∀ j, (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) = y j ()) →
        forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F s y =
          2 * (allocatedBufferedTorusCutoff (R := R) U b o r hr (coveredJetAmbientTorus U d y) : ℂ) *
            g (s, fun a => (((u a.1).val a.2 / period : ℝ) : UnitAddCircle)) := by
  classical
  let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
  let coordinates := fun v : (Σ j, J j) → ℝ =>
    allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered v)
  have hcoord : LipschitzWith Lcoord coordinates := by
    simpa only [Lcoord, coordinates, mul_one, Function.comp_def] using
      (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR Cforward hforward K hK).comp
        singleSiteFromLayered_lipschitz
  have hprod : LipschitzWith (max 1 Lcoord)
      (fun p : Y × ((Σ j, J j) → ℝ) => (p.1, coordinates p.2)) := by
    simpa only [mul_one, Function.comp_def] using
      (LipschitzWith.prod_fst.prodMk (hcoord.comp LipschitzWith.prod_snd))
  let Fambient := fun a (p : Y × ((Σ j, J j) → ℝ)) => F a (p.1, coordinates p.2)
  have hFl (a) : LipschitzWith (L * max 1 Lcoord) (Fambient a) :=
    (hf a).comp hprod
  have hFb (a) (v) : ‖Fambient a v‖ ≤ (1 : ℝ≥0) := hf1 a _
  obtain ⟨g₀, hg₀, hgb, hgv⟩ := exists_parametric_layered_full_residue_covered_extension
    (fun j => euclideanSubspace (U j)) bW b hb period d hdiv Fambient
      (L * max 1 Lcoord) 1 hFl hFb
  refine ⟨fun z => g₀ z / 2, ?_, ?_, ?_⟩
  · apply lipschitz_complex_div_two
    simpa only [mul_one, Lcoord] using hg₀
  · intro z
    apply complex_div_two_norm_le
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one, mul_one] using hgb z
  · intro s u y hu
    have hcut := allocatedBufferedTorusCutoff_eq_siteChart_s2 U b o r hr hR C hC hchart hbudget B S hb bW d y
    by_cases hc : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y = 0
    · rw [forecastBufferedCoveredSiteFactor_zero_of_cutoff_zero B U b S o hb bW d r hr period F s y hc,
        hcut, hc, mul_zero, zero_mul]
    have hy : y ∈ chart '' region := by
      by_contra hn
      exact hc (restrictedComplexChartDensity_zero _ _ _ _ hn)
    obtain ⟨w, hw, rfl⟩ := hy
    have hu' (j : Fin m) : (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ()), w.2 j ()) := hu j
    have hsmall (j : Fin m) (i : J j) :
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ())) i| ≤ 1 / 4 :=
      (hw j (mem_univ j) () (mem_univ ())).1 i
    have hv := hgv s u (fun j => orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ()))
      (fun j => w.2 j ()) hu' hsmall
    dsimp only [Fambient, coordinates] at hv
    rw [allocatedFullAmbientSiteCoordinates_layered_point (R := R) U b o
      (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())] at hv
    change g₀ _ = F (forecastBufferedFullResidue d period w)
      (s, allocatedFullMixedSiteValue (R := R) U b
        (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())) at hv
    dsimp only
    rw [hv, forecastBufferedCoveredSiteFactor_on_chart B U b S o hb bW d r hr period F s w hw,
      hcut]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {X : Type*} [Fintype X]

theorem exists_forecast_buffered_normalized_twist_s2_oai
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (mask : (X → ZMod period) → ℂ) (hmask : ∀ a, ‖mask a‖ ≤ 1)
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → (X → ℝ) × (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hf : ∀ a, LipschitzWith L (F a)) (hf1 : ∀ a z, ‖F a z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lg := max ((L * max 1 Lcoord) * max 1 (period : ℝ≥0)) (4 * period)
    let Lout := Lcut * period + Lg
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) period period Lout,
      twist.modulus = period ∧ twist.cover = period ∧
      ∀ (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hp : ∀ j e, coefficients (p j) e ∈ U j) (u : X → ℤ),
        mask (fun i => (u i : ZMod period)) *
          forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F
            (fun i => (u i : ℝ) / N i)
            (BooleanCubeKernel.physicalSingleSiteValue U d p hp (fun i => (u i : ℝ))) =
          2 * twist.eval N p u := by
  intro Lcoord Lcut Lg Lout
  obtain ⟨g, hg, hgb, hgv⟩ := exists_forecast_buffered_cover_factor B U b S o hb bW d r hr period
    hdiv hR C hC hchart hbudget Cforward hforward K hK F hf hf1
  let χ := allocatedBufferedTorusCutoff (R := R) U b o r hr
  have hχ := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget
  have hχL : LipschitzWith Lcut χ :=
    allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget Cforward hforward K hK
  have hχCL : LipschitzWith (Lcut * period)
      (fun z : (X → ℝ) × ((Σ j, J j) → UnitAddCircle) =>
        (χ (forecastCoverCutoffInput period z.2) : ℂ)) := by
    simpa only [one_mul, mul_one, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp
        ((hχL.comp (forecastCoverCutoffInput_lipschitz period)).comp LipschitzWith.prod_snd)
  have hχb (z : (X → ℝ) × ((Σ j, J j) → UnitAddCircle)) :
      ‖(χ (forecastCoverCutoffInput period z.2) : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
    exact (hχ _).2
  let smooth := fun z : (X → ℝ) × ((Σ j, J j) → UnitAddCircle) =>
    (χ (forecastCoverCutoffInput period z.2) : ℂ) * g z
  have hsmooth : LipschitzWith Lout smooth := by
    simpa only [one_mul, mul_one, add_comm, Function.comp_def, smooth, Lout, Lg] using
      lipschitz_mul_of_bounds _ _ hχCL hg (Bf := 1) (Bg := 1) hχb hgb
  have hsmoothb (z) : ‖smooth z‖ ≤ 1 := by
    dsimp only [smooth]
    rw [norm_mul]
    exact (mul_le_mul (hχb z) (hgb z) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  let twist : NormalizedPolynomialTwist X (Σ j, J j) period period Lout :=
    { modulus := period
      modulus_pos := Nat.pos_of_ne_zero (NeZero.ne period)
      modulus_bound := le_rfl
      cover := period
      cover_pos := Nat.pos_of_ne_zero (NeZero.ne period)
      cover_bound := le_rfl
      mask := mask
      mask_bound := hmask
      smooth := smooth
      smooth_bound := hsmoothb
      smooth_lipschitz := hsmooth }
  refine ⟨twist, rfl, rfl, ?_⟩
  intro N p hp u
  have h := hgv (fun i => (u i : ℝ) / N i)
    (BooleanCubeKernel.physicalEuclideanSitePoint U p hp (fun i => (u i : ℝ)))
    (BooleanCubeKernel.physicalSingleSiteValue U d p hp (fun i => (u i : ℝ)))
    (fun j => (BooleanCubeKernel.physicalSingleSiteValue_eq_mk U p hp d
      (fun i => (u i : ℝ)) j).symm)
  rw [BooleanCubeKernel.physicalSingleSiteValue_ambient] at h
  simp only [BooleanCubeKernel.physicalEuclideanSitePoint_apply] at h
  dsimp only [NormalizedPolynomialTwist.eval, twist, smooth]
  rw [forecastCoverCutoffInput_physicalGridFactorInput]
  rw [h]
  dsimp only [χ]
  unfold physicalGridFactorInput
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.exists_forecast_buffered_normalized_twist_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.exists_forecast_buffered_normalized_twist_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
