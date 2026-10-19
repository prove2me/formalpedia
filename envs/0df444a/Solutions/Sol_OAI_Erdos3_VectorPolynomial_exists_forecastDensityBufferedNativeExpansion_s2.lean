-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedNativeExpansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:31:13.628342+00:00
-- url     : https://prove2.me/submissions/5b40b857-2843-431a-bbbe-f49f21586cbe

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedBufferedTorusCutoff_eq_siteChart_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastDensityBufferedPhysicalAtom_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SitePlateauCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem finite_site_cutoff_error {T S : Type*} [Fintype T] [Fintype S]
    (target : ℂ) (c : T → ℂ) (f : T → S → ℂ) (χ : S → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (hkeep : target ≠ 0 → ∀ s, χ s = 1)
    (he : (∀ s, χ s ≠ 0) → ‖target - ∑ k, c k * ∏ s, f k s‖ ≤ ε) :
    ‖target - ∑ k, c k * ∏ s, χ s * f k s‖ ≤ ε := by
  have hid : (∑ k, c k * ∏ s, χ s * f k s) =
      (∏ s, χ s) * ∑ k, c k * ∏ s, f k s := by
    simp only [Finset.prod_mul_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have ht : (∏ s, χ s) * target = target := by
    by_cases hz : target = 0
    · simp only [hz, mul_zero]
    · simp only [hkeep hz, Finset.prod_const_one, one_mul]
  rw [hid, ← ht, ← mul_sub, norm_mul]
  by_cases hz : ∃ s, χ s = 0
  · obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hs, norm_zero, zero_mul]
    exact hε
  · have hp : ‖∏ s, χ s‖ ≤ 1 := by
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun s _ => hχ s)).trans_eq
        (Finset.prod_const_one)
    exact (mul_le_mul hp (he (fun s hs => hz ⟨s, hs⟩)) (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)

end Erdos3

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem forecastBufferedTwist_lipschitz_exp_bound {P : ℝ} (hP : 0 ≤ P)
    (q : ℕ) (L Lcoord Lcut : ℝ≥0)
    (hq : (q : ℝ) ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (hcoord : (Lcoord : ℝ) ≤ Real.exp P) (hcut : (Lcut : ℝ) ≤ Real.exp P) :
    ((Lcut * q + max ((L * max 1 Lcoord) * max 1 (q : ℝ≥0)) (4 * q) : ℝ≥0) : ℝ) ≤
      Real.exp (3 * P + 3) := by
  have hone : (1 : ℝ) ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have he2 : Real.exp P * Real.exp P = Real.exp (2 * P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he3 : Real.exp (2 * P) * Real.exp P = Real.exp (3 * P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : (L : ℝ) * max 1 (Lcoord : ℝ) * max 1 (q : ℝ) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ (Real.exp P * Real.exp P) * Real.exp P :=
        mul_le_mul (mul_le_mul hL (max_le hone hcoord) (by positivity) (Real.exp_pos _).le)
          (max_le hone hq) (by positivity) (by positivity)
      _ = _ := by rw [he2, he3]
  have hfirst : (Lcut : ℝ) * q ≤ Real.exp (2 * P) := by
    exact (mul_le_mul hcut hq (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq he2
  have he23 : Real.exp (2 * P) ≤ Real.exp (3 * P) := Real.exp_le_exp.mpr (by linarith)
  have he13 : Real.exp P ≤ Real.exp (3 * P) := Real.exp_le_exp.mpr (by linarith)
  have hfour : (4 : ℝ) * q ≤ 4 * Real.exp (3 * P) :=
    mul_le_mul_of_nonneg_left (hq.trans he13) (by norm_num)
  have hmax : max ((L : ℝ) * max 1 (Lcoord : ℝ) * max 1 (q : ℝ)) (4 * q) ≤
      4 * Real.exp (3 * P) := max_le (hprod.trans (by nlinarith [Real.exp_pos (3 * P)])) hfour
  have hfive : (5 : ℝ) ≤ Real.exp 3 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h ⊢
    linarith
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_max, NNReal.coe_one,
    NNReal.coe_ofNat]
  calc
    _ ≤ 5 * Real.exp (3 * P) := by linarith [hfirst.trans he23]
    _ ≤ Real.exp 3 * Real.exp (3 * P) :=
      mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

attribute [instance] ActualForecastData.fintypeTerm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPhysicalQuarterRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedCoveredChart_of_integer_deck
    (M : ℕ) [NeZero M] (u : W) (x : W × (Fin n → ℤ)) (deck : E → ℤ)
    (hdeck : normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm deck).val = u) :
    (QuotientAddGroup.mk ((M : ℝ)⁻¹ • u) : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW M (x, integerResidueMap E M deck) := by
  have h := normalizedCoverLift_add_deck W bW b hb M (NeZero.pos M) x deck
  rw [hdeck] at h
  exact h.symm

theorem exists_forecast_individual_cover_transport
    (d : ℕ) [NeZero d] (u : W) (x : W × (Fin n → ℤ)) (r : E → ZMod d)
    (hchart : (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u) : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW d (x, r)) :
    ∃ deck : E → ℤ,
      normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm deck).val = u ∧
      integerResidueMap E d deck = r ∧
      ∀ (M : ℕ) [NeZero M],
        (QuotientAddGroup.mk ((M : ℝ)⁻¹ • u) : W ⧸
          (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
            normalizedCoveredChart W b hb bW M (x, integerResidueMap E M deck) := by
  obtain ⟨deck, hdeck, hr⟩ := exists_covered_representative_offset W bW b hb d
    ((d : ℝ)⁻¹ • u) x r hchart
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at hdeck
  exact ⟨deck, hdeck, hr, fun M _ =>
    normalizedCoveredChart_of_integer_deck W bW b hb M u x deck hdeck⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical NNReal

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

local notation "single" => (fun _ : Fin m => Unit)

include B S in
theorem exists_forecast_physical_quarter_recovery
    (r : ℝ≥0) (hr : 0 < r)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j e, coefficients (p j) e ∈ U j) (t : X → ℝ)
    (hnonzero : allocatedBufferedTorusCutoff (R := R) U b o r hr
      (fun a : JetAmbientIndex single J => (eval t (p a.1) a.2.2 : UnitAddCircle)) ≠ 0) :
    ∃ (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ),
      (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j)
          (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j) ∧
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) := by
  let y := BooleanCubeKernel.physicalSingleSiteValue U 1 p hp t
  let chart := mixedCoveredJetChart (O := single) U o b hb bW 1
  let region := mixedCoveredJetRegion (O := single) (E := E) U o b 1
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
  have hcut := allocatedBufferedTorusCutoff_eq_siteChart_s2 U b o r hr hR C hC hchart hbudget
    B S hb bW 1 y
  rw [BooleanCubeKernel.physicalSingleSiteValue_ambient] at hcut
  have hsite : allocatedBufferedSiteChartFactor B U b S o hb bW 1 r hr (fun _ => 1) y ≠ 0 := by
    rw [← hcut]
    exact_mod_cast hnonzero
  have hy : y ∈ chart '' region := by
    by_contra hnot
    exact hsite (restrictedComplexChartDensity_zero _ _ _ _ hnot)
  obtain ⟨z, hz, he⟩ := hy
  let w := fun j => mixedArrayRegroup (I j) (Fin (n j)) Unit (z.1 j) ()
  have hquarter (j : Fin m) (i : J j) :
      |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4 :=
    (hz j (mem_univ j) () (mem_univ ())).1 i
  have hcovered (j : Fin m) :
      (QuotientAddGroup.mk (((1 : ℕ) : ℝ)⁻¹ • BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j) :
        euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
      normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) 1
        (orthonormalMixedChart (o j) (w j), z.2 j ()) := by
    exact (BooleanCubeKernel.physicalSingleSiteValue_eq_mk U p hp 1 t j).symm.trans
      (congrFun (congrFun he j) ()).symm
  have hlift (j : Fin m) : ∃ deck : E j → ℤ,
      normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j)
        (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm deck).val =
      BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j := by
    obtain ⟨deck, hdeck, _⟩ := exists_forecast_individual_cover_transport
      (euclideanSubspace (U j)) (bW j) (b j) (hb j) 1
      (BooleanCubeKernel.physicalEuclideanSitePoint U p hp t j)
      (orthonormalMixedChart (o j) (w j)) (z.2 j ()) (hcovered j)
    exact ⟨deck, hdeck⟩
  choose deck hdeck using hlift
  exact ⟨w, deck, hdeck, hquarter⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastDensityPhysicalApproximation
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem forecast_single_cutoff_error {T : Type*} [Fintype T]
    (target cutoff : ℂ) (coefficient atom : T → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hcutoff : ‖cutoff‖ ≤ 1)
    (hkeep : target ≠ 0 → cutoff = 1)
    (herror : cutoff ≠ 0 → ‖target - ∑ i, coefficient i * atom i‖ ≤ ε) :
    ‖target - ∑ i, coefficient i * (cutoff * atom i)‖ ≤ ε := by
  simpa only [Finset.univ_unique, Finset.prod_singleton] using
    finite_site_cutoff_error target coefficient (fun i (_ : Unit) => atom i)
      (fun _ : Unit => cutoff) hε (fun _ => hcutoff)
      (fun ht _ => hkeep ht) (fun ht => by
        simpa only [Finset.univ_unique, Finset.prod_singleton] using herror (ht ()))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem forecastPhysicalBufferedError
    {U V T : Type*} [Fintype T]
    (target : U → ℂ) (coefficient : T → ℂ) (atom : T → U → V → ℂ)
    (cutoff : U → ℝ) (W : T → U → ℂ) (Good : U → V → Prop)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrange : ∀ u, 0 ≤ cutoff u ∧ cutoff u ≤ 1)
    (hrepresent : ∀ u, cutoff u ≠ 0 → ∃ w, Good u w)
    (hidentity : ∀ t u w, Good u w → (cutoff u : ℂ) * atom t u w = 2 * W t u)
    (hzero : ∀ t u, cutoff u = 0 → W t u = 0)
    (hkeep : ∀ u, target u ≠ 0 → cutoff u = 1)
    (herror : ∀ u w, Good u w → ‖target u - ∑ t, coefficient t * atom t u w‖ ≤ ε) :
    ∀ u, ‖target u - ∑ t, (2 * coefficient t) * W t u‖ ≤ ε := by
  intro u
  by_cases hc : cutoff u = 0
  · have ht : target u = 0 := by
      by_contra hn
      have hk := hkeep u hn
      rw [hc] at hk
      exact zero_ne_one hk
    simpa only [ht, hzero _ _ hc, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero]
      using hε
  · obtain ⟨w, hw⟩ := hrepresent u hc
    have hbound : ‖(cutoff u : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hrange u).1]
      exact (hrange u).2
    have he := forecast_single_cutoff_error (target u) (cutoff u : ℂ)
      coefficient (fun t => atom t u w) hε hbound
      (fun ht => by rw [hkeep u ht, Complex.ofReal_one]) (fun _ => herror u w hw)
    have hsum : (∑ t, coefficient t * ((cutoff u : ℂ) * atom t u w)) =
        ∑ t, (2 * coefficient t) * W t u := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hidentity t u w hw]
      ring
    rwa [hsum] at he

theorem forecastPhysicalBufferedCoefficientMass
    {T : Type*} [Fintype T] (coefficient : T → ℂ) {mass : ℝ}
    (hmass : (∑ t, ‖coefficient t‖) ≤ mass) :
    (∑ t, ‖(2 : ℂ) * coefficient t‖) ≤ 2 * mass := by
  calc
    _ = ∑ t, 2 * ‖coefficient t‖ := by norm_num [norm_mul]
    _ = 2 * ∑ t, ‖coefficient t‖ := (Finset.mul_sum ..).symm
    _ ≤ 2 * mass := mul_le_mul_of_nonneg_left hmass (by norm_num)

end Erdos3

end

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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

include hR hbound hLips in
theorem exists_forecastDensityBufferedNativeExpansion_s2_oai
    {A Site Term : Type*} [Fintype A] [Fintype Term]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : Term → AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (e : Term → A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : Term → A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ t a, (e t a).Bounds (Tsite t a) (Dsite t a) (Csite t a) Lsite (Hsite t a))
    (k : ∀ t a, (e t a).Term) (site : Site)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤
      Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (bufferRadius : ℝ≥0) (hbuffer : 0 < bufferRadius)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      Cinv j * ‖v‖)
    (hbudget : ∀ j, Cinv j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (bufferRadius : ℝ) * R j)) ≤ 1 / 4) :
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lsite) * Lspatial
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * bufferRadius)) * Lcoord
    let period := fun t => orderOf (χ t) * commonSitePeriod (e t) (k t)
    ∀ {P : ℝ}, 0 ≤ P →
      (∀ t, (period t : ℝ) ≤ Real.exp P) →
      (Lfactor : ℝ) ≤ Real.exp P → (Lcoord : ℝ) ≤ Real.exp P →
      (Lcut : ℝ) ≤ Real.exp P →
    ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩,
      (∀ t, (twists t).modulus = period t ∧ (twists t).cover = period t) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hpoly : ∀ j v, coefficients (poly j) v ∈ U j)
        (coefficient : Term → ℂ) (target : (X → ℤ) → ℂ) (mass ε : ℝ),
        (∑ t, ‖coefficient t‖) ≤ mass → 0 ≤ ε →
        (∀ u, target u ≠ 0 → allocatedBufferedTorusCutoff (R := R) U basis o
          bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1) →
        (∀ (u : X → ℤ) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
          (deck : ∀ j, Eout j → ℤ),
          (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
            (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
              physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) →
          (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
            (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
          ‖target u - ∑ t, coefficient t *
            forecastDensityNormalizedAtom B U basis S density cap selected (χ t) (e t) (k t) site
              base physicalN τ u deck w‖ ≤ ε) →
        (∑ t, ‖(2 : ℂ) * coefficient t‖) ≤ 2 * mass ∧
        ∀ u, ‖target u - ∑ t, ((2 : ℂ) * coefficient t) *
          (twists t).eval physicalN poly u‖ ≤ ε := by
  intro Lspatial Lfactor Lcoord Lcut period P hP hperiod hfactor hcoord hcut
  have hone (t : Term) : ∃ twist : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩,
      twist.modulus = period t ∧ twist.cover = period t ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ),
        (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
          (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
            physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
          (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        (allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) : ℂ) *
          forecastDensityNormalizedAtom B U basis S density cap selected (χ t) (e t) (k t) site
            base physicalN τ u deck w = 2 * twist.eval physicalN poly u) ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
        allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 0 →
        twist.eval physicalN poly u = 0) := by
    have hpos : 0 < period t := Nat.mul_pos (zmod_character_order_pos (χ t))
      (commonSitePeriod_pos (e t) (he t) (k t))
    let _ : NeZero (period t) := ⟨hpos.ne'⟩
    obtain ⟨twist, hmod, hcover, hvalue, hzero⟩ :=
      exists_forecastDensityBufferedPhysicalAtom_s2 (X := X)
        B U basis hR S density cap lip hbound hLips selected hR1 (χ t) (period t) (dvd_mul_right _ _)
        (e t) (he t) (k t) site
        (fun a => (commonSitePeriod_dvd (e t) (k t) a).trans (dvd_mul_left _ _))
        base physicalN τ hτ o bW hb Cforward hforward K hK
        bufferRadius hbuffer Cinv hCinv hchart hbudget
    have hp' : (period t : ℝ) ≤ Real.exp (3 * P + 3) :=
      (hperiod t).trans (Real.exp_le_exp.mpr (by linarith))
    have hLip := forecastBufferedTwist_lipschitz_exp_bound hP
      (period t) Lfactor Lcoord Lcut (hperiod t) hfactor hcoord hcut
    let result : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩ :=
      twist.mono hp' hp' (show _ ≤ (⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩ : ℝ≥0)
        from hLip)
    refine ⟨result, hmod, hcover, ?_, hzero⟩
    intro poly hpoly u w deck hdeck hquarter
    have h := hvalue poly hpoly u w deck hdeck hquarter
    have hH : ((((cap : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (cap : ℝ) + 1 ≠ 0 by positivity)
    unfold forecastDensityNormalizedAtom
    rw [← mul_div_assoc, h]
    dsimp only [result, NormalizedPolynomialTwist.eval_mono]
    field_simp
    rfl
  choose twists hmod hcover hvalue hzero using hone
  refine ⟨twists, fun t => ⟨hmod t, hcover t⟩, ?_⟩
  intro poly hpoly coefficient target mass ε hmass hε hkeep herror
  refine ⟨forecastPhysicalBufferedCoefficientMass coefficient hmass, ?_⟩
  let cutoff := fun u : X → ℤ => allocatedBufferedTorusCutoff (R := R) U basis o
    bufferRadius hbuffer
    (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle))
  let Good := fun (u : X → ℤ)
      (v : (∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) × (∀ j, Eout j → ℤ)) =>
    (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (v.1 j)) + ((bW j).equivFun.symm (v.2 j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) ∧
    (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (v.1 j)) i| ≤ 1 / 4)
  apply forecastPhysicalBufferedError target coefficient
    (fun t u v => forecastDensityNormalizedAtom B U basis S density cap selected (χ t) (e t) (k t) site base physicalN τ u v.2 v.1)
    cutoff (fun t u => (twists t).eval physicalN poly u) Good hε
  · intro u
    exact allocatedBufferedTorusCutoff_range U basis o bufferRadius hbuffer hR
      Cinv hCinv hchart hbudget _
  · intro u hu
    obtain ⟨w, deck, hd, hq⟩ := exists_forecast_physical_quarter_recovery B U basis S o hb bW
      bufferRadius hbuffer hR Cinv hCinv hchart hbudget poly hpoly
      (fun i => (u i : ℝ)) hu
    exact ⟨(w, deck), hd, hq⟩
  · intro t u v hv
    exact hvalue t poly hpoly u v.1 v.2 hv.1 hv.2
  · intro t u hu
    exact hzero t poly hpoly u hu
  · exact hkeep
  · intro u v hv
    exact herror u v.1 v.2 hv.1 hv.2

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9, u_10} : type_of% @OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedNativeExpansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9, u_10} := @OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedNativeExpansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9, u_10}
