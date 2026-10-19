-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_cover_site_expansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:16:15.549273+00:00
-- url     : https://prove2.me/submissions/0997fccb-bc41-4c13-9080-435c2e4eaf4e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196

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

theorem exists_quarter_cover_extension {D : Type*} [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧
      (∀ a x, (∀ i, |x i| ≤ 1 / 4) → g (quarterCoverPoint q a x) = f a x) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_bounded_extension_on_separated_charts
    (quarterCoverPoint (D := D) q) {x | ∀ i, |x i| ≤ 1 / 4}
    (q : ℝ≥0) (2 * q) L B
    (fun a x hx y hy => quarterCoverPoint_within q a hx hy)
    (by
      intro a b hab x hx y hy
      simpa using quarterCoverPoint_separated q hab hx hy)
    f (fun a => (hf a).lipschitzOnWith) (fun a x _ => hb a x)
  refine ⟨g, ?_, hvalue, hbound⟩
  have heq : 2 * B * (2 * (q : ℝ≥0)) = 4 * B * q := by ring
  simpa only [heq] using hg

theorem exists_integer_quarter_cover_extension {D : Type*} [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (a : D → ℤ) (x : D → ℝ), (∀ i, |x i| ≤ 1 / 4) →
        g (fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle)) = f (fun i => (a i : ZMod q)) x := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_quarter_cover_extension q f L B hf hb
  refine ⟨g, hg, hbound, ?_⟩
  intro a x hx
  rw [← quarterCoverPoint_intCast]
  exact hvalue (fun i => (a i : ZMod q)) x hx

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix NNReal Classical

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

theorem exists_normalized_sheet_residue_map :
    ∃ r : (D → ZMod q) → (Fin n → ZMod q), ∀ (z : Fin n → ℤ) (w : I → ℤ),
      r (fun i => (latticeDeckInteger W bW b hb z w i : ZMod q)) = fun i => (z i : ZMod q) := by
  obtain ⟨A, _hA, hres⟩ := standardLatticeCoordinates_residue W bW b hb q
  refine ⟨fun a i => (integerResidueMatrix A q *ᵥ a) (Sum.inl i), ?_⟩
  intro z w
  funext i
  change (integerResidueMatrix A q *ᵥ
    integerResidueMap D q (latticeDeckInteger W bW b hb z w)) (Sum.inl i) = _
  rw [← hres, latticeDeckInteger_coordinates]
  rfl

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped NNReal Classical

variable {M : Type*} [Fintype M] {D E : M → Type*}
variable [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)]
variable {n : M → ℕ}
variable (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
variable (q : ℕ) [NeZero q]

local notation "ambient" => (Σ j : M, D j)

include bW in
theorem exists_layered_cover_site_extension
    (f : (∀ j, Fin (n j) → ZMod q) → (ambient → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (u : ∀ j, W j) (x : ∀ j, W j × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : W j ⧸
          (latticeSection (standardEuclideanLattice (D j)) (W j)).toAddSubgroup) =
            normalizedLatticeQuotient (W j) (b j) (hb j) (x j)) →
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (fun a => ((((u a.1).val a.2) / q : ℝ) : UnitAddCircle)) =
          f (fun j i => ((x j).2 i : ZMod q))
            (fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  choose r hr using (fun j => exists_normalized_sheet_residue_map (W j) (bW j) (b j) (hb j) q)
  let R : (ambient → ZMod q) → (∀ j, Fin (n j) → ZMod q) :=
    fun a j => r j (fun i => a ⟨j, i⟩)
  let F := fun a v => f (R a) v
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_integer_quarter_cover_extension q F L B
    (fun a => hf (R a)) (fun a v => hbound (R a) v)
  refine ⟨g, hg, hgb, ?_⟩
  intro u x hu hx
  choose w hw using (fun j => exists_normalized_representative_offset
    (W j) (bW j) (b j) (hb j) (u j) (x j) (hu j))
  let β : ambient → ℤ := fun a => latticeDeckInteger (W a.1) (bW a.1) (b a.1) (hb a.1)
    (x a.1).2 (w a.1) a.2
  let v : ambient → ℝ := fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2
  have hrβ : R (fun a => (β a : ZMod q)) = fun j i => ((x j).2 i : ZMod q) := by
    funext j
    exact hr j (x j).2 (w j)
  have heq := hvalue β v (fun a => hx a.1 a.2)
  change g (fun a => ((((β a : ℝ) + v a) / q : ℝ) : UnitAddCircle)) =
    f (R (fun a => (β a : ZMod q))) v at heq
  rw [hrβ] at heq
  have hpoint : (fun a => ((((β a : ℝ) + v a) / q : ℝ) : UnitAddCircle)) =
      fun a => ((((u a.1).val a.2) / q : ℝ) : UnitAddCircle) := by
    funext a
    rcases a with ⟨j, i⟩
    have h := normalizedDeckPoint_identity (W j) (bW j) (b j) (hb j) (x j) (w j)
    rw [hw j] at h
    have hi := congrArg (fun z : EuclideanSpace ℝ (D j) => z i) h
    change (u j).val i = v ⟨j, i⟩ + (β ⟨j, i⟩ : ℝ) at hi
    rw [hi, add_comm (β ⟨j, i⟩ : ℝ)]
  simpa only [hpoint] using heq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

theorem finite_site_product_coefficient_norm (c : ∀ a, I a → ℂ) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) = ∏ a, ∑ k, ‖c a k‖ := by
  simp only [norm_prod, Fintype.prod_sum]

theorem finite_site_product_coefficient_norm_le (c : ∀ a, I a → ℂ)
    (C : A → ℝ) (hc : ∀ a, (∑ k, ‖c a k‖) ≤ C a) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) ≤ ∏ a, C a := by
  rw [finite_site_product_coefficient_norm]
  exact Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun a _ => hc a)

theorem finite_site_axis_product_lipschitz (f : A → ℝ → ℂ) (L : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hn : ∀ a x, ‖f a x‖ ≤ 1) :
    (∀ x : A → ℝ, ‖∏ a, f a (x a)‖ ≤ 1) ∧
      LipschitzWith (Fintype.card A * L) (fun x : A → ℝ => ∏ a, f a (x a)) := by
  have hl (a : A) : LipschitzWith L (fun x : A → ℝ => f a (x a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((hf a).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y a) L.coe_nonneg)
  simpa only [NNReal.coe_one, one_pow, mul_one] using
    bounded_lipschitz_fintype_prod (fun a (x : A → ℝ) => f a (x a))
      (B := 1) le_rfl hl (fun a x => hn a (x a))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

include h in
omit [Fintype S] in
theorem siteFamily_coefficient_le : (∑ k, ‖siteFamilyCoefficient e k‖) ≤ ∏ a, C a :=
  finite_site_product_coefficient_norm_le (fun a => (e a).coefficient) C
    (fun a => (h a).coefficient_le)

include h in
omit [Fintype S] in
theorem siteFamilyFactor_bounds (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖siteFamilyFactor e k s r x‖ ≤ 1) ∧
      LipschitzWith (Fintype.card A * L) (siteFamilyFactor e k s r) := by
  exact finite_site_axis_product_lipschitz (fun a => (e a).factor (k a) s (r a)) L
    (fun a => (h a).lipschitz (k a) s (r a)) (fun a => (h a).factor_bound (k a) s (r a))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)

theorem commonSitePeriod_dvd (k : ∀ a, (e a).Term) (a : A) :
    (e a).period (k a) ∣ commonSitePeriod e k :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ a)

theorem commonSitePeriod_pos {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a)) (k : ∀ a, (e a).Term) :
    0 < commonSitePeriod e k :=
  Finset.prod_pos (fun a _ => (he a).period_pos (k a))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {A D S : Type*} [Fintype A] [Fintype D]

theorem scaledSiteCoordinates_lipschitz (selected : A → D) (scale : A → ℝ)
    (Q : ℝ≥0) (hQ : ∀ a, |scale a| ≤ Q) :
    LipschitzWith Q (scaledSiteCoordinates selected scale) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  change |scale a * x (selected a) - scale a * y (selected a)| ≤ _
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y (selected a)) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (hQ a) dist_nonneg)

variable (e : A → ScalarSiteExpansion S) (selected : A → D) (scale : A → ℝ)

theorem scaledSiteFamilyFactor_bounds {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, |scale a| ≤ Q)
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖scaledSiteFamilyFactor e selected scale k s r x‖ ≤ 1) ∧
      LipschitzWith ((Fintype.card A * L) * Q) (scaledSiteFamilyFactor e selected scale k s r) := by
  have hf := siteFamilyFactor_bounds e h k s r
  exact ⟨fun x => hf.1 _, hf.2.comp (scaledSiteCoordinates_lipschitz selected scale Q hQ)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.GridNormalizationTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem grid_rescale_coordinate {K : ℝ} (hK : K ≠ 0) (N z : ℝ) :
    (K / N) * (z / K) = z / N := by
  calc
    _ = (K / K) * (z / N) := by ring
    _ = _ := by rw [div_self hK, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hR in
theorem allocatedPrincipalGridScale_pos_of_radius : 0 < scale := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (principalProfileSize_pos (hR j) _)
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))

include hR in
theorem allocatedPrincipalChartRatio_pos :
    0 < allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i := by
  exact div_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i))

include hR in
theorem allocatedPrincipalChartRatio_le :
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i ≤
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) / R j := by
  have hN : (0 : ℝ) < scale :=
    Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i)
  have hg : 0 < gamma := principalProfileSize_pos (hR j) _
  have hlow : gamma * (basisAxisScale (basis j) i : ℝ) ≤ scale := Nat.le_ceil _
  calc
    _ ≤ 1 / gamma := (div_le_div_iff₀ hN hg).mpr (by nlinarith)
    _ = _ := by
      unfold principalProfileSize
      field_simp

theorem allocatedPrincipalChartRatio_coordinate (z : ℝ) :
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i *
        (z / basisAxisScale (basis j) i) = z / scale :=
  grid_rescale_coordinate (Nat.cast_ne_zero.mpr (basisAxisScale_pos (basis j) i).ne') _ _

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNaturalFullSiteScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "slots" => Finset.card (layerIntegerPrincipalSlots (G := G) B j i)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i

include hR in
theorem allocatedNaturalFullSiteRatio_pos :
    0 < allocatedNaturalFullSiteRatio (G := G) B U b (R := R) j i :=
  mul_pos (hR j) (allocatedPrincipalChartRatio_pos B U b hR j i)

include hR in
theorem allocatedNaturalFullSiteRatio_le :
    allocatedNaturalFullSiteRatio (G := G) B U b (R := R) j i ≤ 8 * ((slots : ℝ) + 1) := by
  have h := mul_le_mul_of_nonneg_left (allocatedPrincipalChartRatio_le (G := G) B U b hR j i) (hR j).le
  calc
    _ ≤ R j * (8 * ((slots : ℝ) + 1) / R j) := h
    _ = _ := by field_simp [(hR j).ne']

include hR in
theorem allocatedNaturalFullSiteRatio_coordinate (z : ℝ) :
    allocatedNaturalFullSiteRatio (G := G) B U b (R := R) j i *
      (z / basisAxisScale (b j) i / R j) = z / scale := by
  rw [allocatedNaturalFullSiteRatio]
  calc
    _ = allocatedPrincipalChartRatio (G := G) B U b (R := R) j i *
        (z / basisAxisScale (b j) i) := by field_simp [(hR j).ne']
    _ = _ := allocatedPrincipalChartRatio_coordinate B U b j i z

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFullGridSiteFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ}
variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)
variable (selected : A → Σ j : Fin m, Fin (n j))

local notation "index" => fun a : A => (Sigma.mk (Sigma.fst (selected a)) (Sum.inr (Sigma.snd (selected a))) : LayerSamplerAxis I n)
local notation "ratio" => fun a : A => allocatedNaturalFullSiteRatio (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "scale" => fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))

theorem allocatedFullGridSiteFactor_bounds (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r x‖ ≤ 1) ∧
      LipschitzWith ((Fintype.card A * L) * Q)
        (allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r) := by
  apply scaledSiteFamilyFactor_bounds e (index) (ratio) h Q _ k s r
  intro a
  rw [abs_of_pos (allocatedNaturalFullSiteRatio_pos B U b hR (selected a).1 (selected a).2)]
  exact (allocatedNaturalFullSiteRatio_le B U b hR (selected a).1 (selected a).2).trans (hQ a)

omit [∀ j, Fintype (I j)] in
theorem allocatedFullGridSiteFactor_point (hR : ∀ j, 0 < R j)
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a)))
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r
        (allocatedFullMixedSiteValue (R := R) U b w) =
      siteFamilyFactor e k s r (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  apply congrArg (siteFamilyFactor e k s r)
  funext a
  exact allocatedNaturalFullSiteRatio_coordinate B U b hR (selected a).1 (selected a).2 _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))
variable (k : ∀ a, (e a).Term) (s : S)

local notation "period" => commonSitePeriod e k
local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_cover_site_factor (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ g : ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * period) (4 * period)) g ∧
      (∀ y, ‖g y‖ ≤ 2) ∧
      ∀ (u : ∀ j, euclideanSubspace (U j)) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w j))) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        g (fun a => ((((u a.1).val a.2) / period : ℝ) : UnitAddCircle)) =
          siteFamilyFactor e k s (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
            (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  classical
  let : NeZero period := ⟨(commonSitePeriod_pos e he k).ne'⟩
  let residue := fun (r : ∀ j, Fin (n j) → ZMod period) (a : A) =>
    ZMod.castHom (commonSitePeriod_dvd e k a) (ZMod ((e a).period (k a))) (r (selected a).1 (selected a).2)
  let F := fun (r : ∀ j, Fin (n j) → ZMod period) (v : (Σ j, J j) → ℝ) =>
    allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s (residue r)
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered v))
  have hF (r : ∀ j, Fin (n j) → ZMod period) :
      LipschitzWith (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j))) (F r) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    have hc := (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR Cforward hforward K hK).dist_le_mul
      (singleSiteFromLayered v) (singleSiteFromLayered w)
    have hs := singleSiteFromLayered_lipschitz.dist_le_mul v w
    simp only [NNReal.coe_one, one_mul] at hs
    have hd := hc.trans (mul_le_mul_of_nonneg_left hs (NNReal.coe_nonneg _))
    have ht := (allocatedFullGridSiteFactor_bounds B U b e selected hR he Q hQ k s (residue r)).2.dist_le_mul
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered v))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered w))
    simpa only [NNReal.coe_mul, mul_assoc] using
      ht.trans (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))
  have hB (r : ∀ j, Fin (n j) → ZMod period) (v : (Σ j, J j) → ℝ) : ‖F r v‖ ≤ 1 :=
    (allocatedFullGridSiteFactor_bounds B U b e selected hR he Q hQ k s (residue r)).1 _
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_layered_cover_site_extension
    (fun j => euclideanSubspace (U j)) bW b hb period F
    (((Fintype.card A * L) * Q) * (K * ∑ j, Cforward j * Fintype.card (J j))) 1 hF hB
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa only [mul_one] using hg
  · simpa using hgb
  · intro u w hu hw
    have hval := hvalue u (fun j => orthonormalMixedChart (o j) (w j)) hu hw
    change g _ = allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
      (fun a => ZMod.castHom (commonSitePeriod_dvd e k a) (ZMod ((e a).period (k a)))
        ((w (selected a).1).2 (selected a).2 : ZMod period))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered
        (fun a : Σ j, J j => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
          (orthonormalMixedChart (o a.1) (w a.1)) a.2))) at hval
    simp only [map_intCast] at hval
    rw [allocatedFullAmbientSiteCoordinates_layered_point,
      allocatedFullGridSiteFactor_point B U b e selected hR k s] at hval
    exact hval

end Erdos3.VectorPolynomial

end

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

theorem two_scaled_product_identity {S : Type*} [Fintype S] (c : ℂ) (f : S → ℂ) :
    ((2 : ℂ) ^ Fintype.card S * c) * (∏ s, f s / 2) = c * ∏ s, f s := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  have h2 : (2 : ℂ) ^ Fintype.card S ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [h2]

attribute [local instance] ScalarSiteExpansion.termFinite

theorem coverSiteCoefficient_bound {A S : Type*} [Fintype A] [Fintype S]
    (e : A → ScalarSiteExpansion S) {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a)) :
    (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card S * ∏ a, C a := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  simp only [coverSiteCoefficient, norm_mul, norm_pow, h2, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (siteFamily_coefficient_le e he) (by positivity)

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))

local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_cover_site_expansion_s2_oai (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ g : (∀ a, (e a).Term) → S → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card S * ∏ a, C a ∧
      ∀ (u : S → ∀ j, euclideanSubspace (U j)) (w : S → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ s j, (QuotientAddGroup.mk (u s j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w s j))) →
        (∀ s j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w s j)) i| ≤ 1 / 4) →
        (∑ k, coverSiteCoefficient e k * ∏ s,
          g k s (fun a => ((((u s a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle))) =
          siteFamilyEval e (fun s a => (w s (selected a).1).2 (selected a).2)
            (fun s a => ((w s (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  have hex (k : ∀ a, (e a).Term) (s : S) := exists_allocated_cover_site_factor (G := G)
    B U b e selected k s hR he Q hQ o Cforward hforward K hK hb bW
  choose raw hLip hNorm hValue using hex
  let g := fun k s v => raw k s v / 2
  refine ⟨g, ?_, coverSiteCoefficient_bound e he, ?_⟩
  · intro k s
    exact ⟨lipschitz_complex_div_two (raw k s) _ (hLip k s),
      fun v => complex_div_two_norm_le (hNorm k s v)⟩
  · intro u w hu hw
    have hv (k : ∀ a, (e a).Term) (s : S) := hValue k s (u s) (w s) (hu s) (hw s)
    dsimp only [g]
    simp_rw [hv]
    unfold siteFamilyEval coverSiteCoefficient
    apply Finset.sum_congr rfl
    intro k _
    exact two_scaled_product_identity (siteFamilyCoefficient e k) _

end VectorPolynomial
end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_cover_site_expansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.Erdos3.VectorPolynomial.exists_allocated_cover_site_expansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
