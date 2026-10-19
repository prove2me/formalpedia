-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedPhysicalAtom_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:32:08.831128+00:00
-- url     : https://prove2.me/submissions/2954e4d5-04a4-443e-a44c-256d3c699072

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedBufferedTorusCutoff_eq_siteChart_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecast_buffered_normalized_twist_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

theorem exists_characterOrder_descent {I : Type*} {N : ℕ} [NeZero N]
    (χ : AddChar (I → ZMod N) ℂ) :
    ∃ ψ : AddChar (I → ZMod (orderOf χ)) ℂ,
      characterPullback (zmodPiReduction (zmod_character_order_dvd χ)) ψ = χ ∧
      orderOf ψ = orderOf χ ∧
      (∀ x, χ x = ψ (zmodPiReduction (zmod_character_order_dvd χ) x)) ∧
      ∀ b : I → ℤ, χ (fun i => (b i : ZMod N)) =
        ψ (fun i => (b i : ZMod (orderOf χ))) := by
  obtain ⟨ψ, hpull, horder⟩ := exists_zmodPiReduction_character
    (zmod_character_order_dvd χ) χ (pow_orderOf_eq_one χ)
  have hpoint (x : I → ZMod N) :
      χ x = ψ (zmodPiReduction (zmod_character_order_dvd χ) x) :=
    (congrArg (fun η : AddChar (I → ZMod N) ℂ => η x) hpull).symm
  refine ⟨ψ, hpull, horder, hpoint, ?_⟩
  intro b
  have hred : zmodPiReduction (zmod_character_order_dvd χ)
      (fun i => (b i : ZMod N)) = (fun i => (b i : ZMod (orderOf χ))) := by
    funext i
    exact map_intCast (ZMod.castHom (zmod_character_order_dvd χ) (ZMod (orderOf χ))) (b i)
  rw [hpoint, hred]

end Erdos3

end

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

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
theorem siteFamilyFactor_bounds (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖siteFamilyFactor e k s r x‖ ≤ 1) ∧
      LipschitzWith (Fintype.card A * L) (siteFamilyFactor e k s r) := by
  exact finite_site_axis_product_lipschitz (fun a => (e a).factor (k a) s (r a)) L
    (fun a => (h a).lipschitz (k a) s (r a)) (fun a => (h a).factor_bound (k a) s (r a))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

theorem forecastCongruenceOutput_eq_add {R : Type*} [AddCommMonoid R]
    (u : X → R) (label : ∀ j, Fin (n j) ⊕ E j → R) :
    forecastCongruenceOutput inactive u label =
      forecastSpatialOutputHom inactive u + forecastCoefficientOutputHom inactive label := by
  funext o
  rcases o with ⟨j, x | i | a⟩ <;>
    simp [forecastCongruenceOutput, forecastSpatialOutputHom, forecastCoefficientOutputHom]

variable [Fintype X] [∀ j, Fintype (E j)]

theorem exists_forecastSpatialCharacterSplit
    {N : ℕ} [NeZero N]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod N) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M) :
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ coeff : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ,
        (∀ u, ‖mask u‖ = 1) ∧ (∀ label, ‖coeff label‖ = 1) ∧
        (∀ (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ),
          χ (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod N)) =
            mask (fun x => (u x : ZMod M)) * coeff (fun j i => (label j i : ZMod M))) ∧
        ∀ (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ),
          star (χ (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod N))) =
            star (mask (fun x => (u x : ZMod M))) *
              star (coeff (fun j i => (label j i : ZMod M))) := by
  obtain ⟨ψ, _, _, _, hψ⟩ := exists_characterOrder_descent χ
  let ψM := ψ.compAddMonoidHom (zmodPiReduction hM)
  let mask := ψM.compAddMonoidHom (forecastSpatialOutputHom (E := E) inactive)
  let coeff := ψM.compAddMonoidHom (forecastCoefficientOutputHom (X := X) inactive)
  have heq (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
      χ (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod N)) =
        mask (fun x => (u x : ZMod M)) * coeff (fun j i => (label j i : ZMod M)) := by
    rw [hψ]
    change ψ _ = ψM (forecastSpatialOutputHom inactive _) *
      ψM (forecastCoefficientOutputHom inactive _)
    rw [← AddChar.map_add_eq_mul, ← forecastCongruenceOutput_eq_add]
    dsimp only [ψM, AddChar.compAddMonoidHom_apply]
    congr 1
    funext o
    rcases o with ⟨j, x | i | a⟩ <;>
      simp [zmodPiReduction, forecastCongruenceOutput]
  refine ⟨mask, coeff, (fun _ => AddChar.norm_apply _ _),
    (fun _ => AddChar.norm_apply _ _), heq, ?_⟩
  intro u label
  rw [heq]
  exact map_mul (starRingEnd ℂ) _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastBufferedIntegerDeckFactor
namespace OAI

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

theorem forecastBufferedCoveredSiteFactor_integer_deck
    (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) {Y : Type*}
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod d) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ)
    (u : ∀ j, euclideanSubspace (U j))
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j)
        (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val = u j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    let y : EuclideanJetLayers U single := fun j _ => QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j)
    forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr d F s y =
      allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y *
        F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod d))
          (fun i => (deck j i : ZMod d))) (s, allocatedFullMixedSiteValue (R := R) U b w) := by
  let z : MixedCoveredJetSource I single E n d :=
    (fun j => (fun i _ => (w j).1 i, fun i _ => (w j).2 i),
      fun j _ => integerResidueMap (E j) d (deck j))
  have hz : z ∈ mixedCoveredJetRegion (O := single) (E := E) U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
    intro j _ t _
    exact ⟨hquarter j, mem_univ _⟩
  have hchart : mixedCoveredJetChart U o b hb bW d z =
      fun j (_ : Unit) => QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) := by
    funext j t
    exact (normalizedCoveredChart_of_integer_deck (euclideanSubspace (U j)) (bW j) (b j) (hb j)
      d (u j) (orthonormalMixedChart (o j) (w j)) (deck j) (hdeck j)).symm
  have h := forecastBufferedCoveredSiteFactor_on_chart B U b S o hb bW d r hr d F s z hz
  rw [hchart] at h
  have hres : forecastBufferedFullResidue d d z = fun j =>
      Sum.elim (fun i => ((w j).2 i : ZMod d)) (fun i => (deck j i : ZMod d)) := by
    funext j i
    cases i with
    | inl i => rfl
    | inr i => exact ZMod.natCast_zmod_val (deck j i : ZMod d)
  rw [hres] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

theorem forecastNormalizedSpatialCoordinates_lipschitz (base : X → ℤ) (N : X → ℕ)
    {τ : ℝ} (hτ : 0 < τ) :
    LipschitzWith ⟨8 / τ, by positivity⟩ (forecastNormalizedSpatialCoordinates base N τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (div_nonneg (by norm_num) hτ.le) dist_nonneg)).mpr
  intro a
  change |8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ -
    8 * (y a.1 - (base a.1 : ℝ) / N a.1) / τ| ≤ (8 / τ) * dist x y
  rw [show 8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ -
    8 * (y a.1 - (base a.1 : ℝ) / N a.1) / τ = (8 / τ) * (x a.1 - y a.1) by ring,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 / τ)]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y a.1) (by positivity)

omit [Fintype X] in
theorem forecastNormalizedSpatialCoordinates_eval (base u : X → ℤ) (N : X → ℕ)
    (τ : ℝ) (a : Σ _ : X, Unit ⊕ Empty) :
    forecastNormalizedSpatialCoordinates base N τ (fun i => (u i : ℝ) / N i) a =
      ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8) := by
  unfold forecastNormalizedSpatialCoordinates
  ring

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (R : Fin m → ℝ)

theorem forecastNormalizedInactiveCoordinates_lipschitz
    (hR : ∀ a, |R (selected a).1| ≤ 1) :
    LipschitzWith 1 (forecastNormalizedInactiveCoordinates (I := I) selected R) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  change |R (selected a).1 * v _ - R (selected a).1 * w _| ≤ dist v w
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_right (hR a) (abs_nonneg _)).trans
    (by simpa only [one_mul, Real.dist_eq] using dist_le_pi_dist v w ⟨(selected a).1, Sum.inr (selected a).2⟩)

theorem forecastNormalizedActiveCoordinates_lipschitz :
    LipschitzWith 1 (forecastNormalizedActiveCoordinates P) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  exact (dist_pi_le_iff dist_nonneg).mpr (fun a => dist_le_pi_dist v w a.1.val)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

omit [∀ j, Fintype (I j)] [Fintype A] in
theorem forecastNormalizedInactiveCoordinates_mixed
    (hR : ∀ j, R j ≠ 0) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastNormalizedInactiveCoordinates selected R
      (allocatedFullMixedSiteValue (R := R) U b w) =
      fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
        basisAxisScale (b (selected a).1) (selected a).2 := by
  funext a
  change R (selected a).1 * (_ / _ / R (selected a).1) = _
  rw [mul_div_cancel₀ _ (hR (selected a).1)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastOriginalSampleResidueFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A Y Site : Type*} [Fintype A] [Fintype Y]
variable (selected : A → Σ j : Fin m, Fin (n j)) (R : Fin m → ℝ)
variable (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (M : ℕ) (hd : ∀ a, (e a).period (k a) ∣ M)

theorem forecastNormalizedResidueFactor_bounds [NeZero M]
    (ψ : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ)
    (f : (Y → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) → ℂ)
    {Lf Lsite : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ 1) (hLf : LipschitzWith Lf f)
    {Tsite Dsite Csite Hsite : A → ℝ}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (hR : ∀ a, |R (selected a).1| ≤ 1)
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M) :
    (∀ x, ‖forecastNormalizedResidueFactor P selected R e k site M hd ψ f label x‖ ≤ 1) ∧
      LipschitzWith (Lf + Fintype.card A * Lsite)
        (forecastNormalizedResidueFactor P selected R e k site M hd ψ f label) := by
  let F := fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
    star (ψ label) * f (x.1, forecastNormalizedActiveCoordinates P x.2)
  let g := fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
    siteFamilyFactor e k site (forecastNormalizedResidues selected e k M hd label)
      (forecastNormalizedInactiveCoordinates selected R x.2)
  have hphase : ‖star (ψ label)‖ = 1 := by
    rw [norm_star, AddChar.norm_apply]
  have hactive : LipschitzWith 1 (fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
      (x.1, forecastNormalizedActiveCoordinates P x.2)) := by
    simpa only [Function.comp_def, one_mul, max_self] using
      (LipschitzWith.prod_fst (α := Y → ℝ) (β := LayerSamplerAxis I n → ℝ)).prodMk
        ((forecastNormalizedActiveCoordinates_lipschitz P).comp LipschitzWith.prod_snd)
  have hFL : LipschitzWith Lf F := by
    have hcomp : LipschitzWith Lf (fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
        f (x.1, forecastNormalizedActiveCoordinates P x.2)) := by
      simpa only [mul_one, Function.comp_def] using hLf.comp hactive
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (star (ψ label) * _) (star (ψ label) * _) ≤ _
    rw [dist_eq_norm, ← mul_sub, norm_mul, hphase, one_mul]
    simpa only [dist_eq_norm] using hcomp.dist_le_mul x y
  have hFb : ∀ x, ‖F x‖ ≤ 1 := by
    intro x
    change ‖star (ψ label) * _‖ ≤ 1
    rw [norm_mul, hphase, one_mul]
    exact hf _
  obtain ⟨hgb, hgL⟩ := siteFamilyFactor_bounds e he k site
    (forecastNormalizedResidues selected e k M hd label)
  have hinactive : LipschitzWith 1 (fun x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ) =>
      forecastNormalizedInactiveCoordinates selected R x.2) := by
    simpa only [one_mul, Function.comp_def] using
      (forecastNormalizedInactiveCoordinates_lipschitz selected R hR).comp
        (LipschitzWith.prod_snd (α := Y → ℝ) (β := LayerSamplerAxis I n → ℝ))
  have hg : LipschitzWith (Fintype.card A * Lsite) g := by
    simpa only [mul_one, Function.comp_def] using hgL.comp hinactive
  have hgn : ∀ x, ‖g x‖ ≤ 1 := fun x => hgb _
  constructor
  · intro x
    change ‖F x * g x‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (hFb x) (hgn x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := (lipschitz_mul_of_bounds
      (X := (Y → ℝ) × (LayerSamplerAxis I n → ℝ))
      F g hFL hg (Bf := 1) (Bg := 1) hFb hgn).dist_le_mul x y
    simpa only [one_mul, add_comm, F, g, forecastNormalizedResidueFactor] using hh

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

omit [∀ j, Fintype (I j)] [Fintype Y] [∀ j, Fintype (E j)] in

theorem forecastNormalizedResidueFactor_mixed
    (ψ : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ)
    (f : (Y → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) → ℂ)
    (hR : ∀ j, R j ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ) (y : Y → ℝ) :
    forecastNormalizedResidueFactor P selected R e k site M hd ψ f
      (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M)) (fun a => (deck j a : ZMod M)))
      (y, allocatedFullMixedSiteValue (R := R) U b w) =
    star (ψ (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M)) (fun a => (deck j a : ZMod M)))) *
      f (y, forecastNormalizedActiveCoordinates P (allocatedFullMixedSiteValue (R := R) U b w)) *
      siteFamilyFactor e k site
        (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
        (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
          basisAxisScale (b (selected a).1) (selected a).2) := by
  unfold forecastNormalizedResidueFactor forecastNormalizedResidues
  simp only [Sum.elim_inl, map_intCast]
  rw [forecastNormalizedInactiveCoordinates_mixed selected R U b hR w]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem forecastDensity_normalized_bounds {Y : Type*} [PseudoMetricSpace Y]
    (density : Y → ℝ) (C L : ℝ≥0) (hbound : ∀ y, |density y| ≤ (C : ℝ))
    (hLips : LipschitzWith L density) :
    let F := fun y => (density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)
    (∀ y, ‖F y‖ ≤ 1) ∧ LipschitzWith L F ∧
      (∀ y, (density y : ℂ) = (((C : ℝ) + 1 : ℝ) : ℂ) * F y) := by
  intro F
  have hpos : (0 : ℝ) < C + 1 := by positivity
  have hden : ‖(((C : ℝ) + 1 : ℝ) : ℂ)‖ = (C : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    change ‖(density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)‖ ≤ 1
    rw [norm_div, hden, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_one hpos).mpr ((hbound y).trans (by linarith))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((density x : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ))
      ((density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)) ≤ (L : ℝ) * dist x y
    rw [dist_eq_norm, ← sub_div, norm_div, ← Complex.ofReal_sub, Complex.norm_real, hden]
    have hd := hLips.dist_le_mul x y
    rw [dist_eq_norm] at hd
    exact (div_le_self (norm_nonneg _) (by linarith [C.coe_nonneg] : (1 : ℝ) ≤ C + 1)).trans hd
  · intro y
    change (density y : ℂ) = (((C : ℝ) + 1 : ℝ) : ℂ) *
      ((density y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ))
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

variable {m : ℕ} {G X Spatial : Type*} [Fintype G] [Fintype X] [Fintype Spatial]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)

include hR in
theorem exists_forecastDensityResidueFactor
    (density : ((Spatial → ℝ) × (Output → ℝ)) → ℝ)
    (C L : ℝ≥0) (hbound : ∀ y, |density y| ≤ (C : ℝ))
    (hLips : LipschitzWith L density)
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {N : ℕ} [NeZero N]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod N) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M) :
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ F : (∀ j, Fin (n j) ⊕ Eout j → ZMod M) →
        ((Spatial → ℝ) × (LayerSamplerAxis I n → ℝ)) → ℂ,
        (∀ u, ‖mask u‖ = 1) ∧
        (∀ label y, ‖F label y‖ ≤ 1) ∧
        (∀ label, LipschitzWith (L + Fintype.card A * Lsite) (F label)) ∧
        ∀ (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (y : Spatial → ℝ),
          (density (y, forecastNormalizedActiveCoordinates short
            (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
            star (χ (fun o => (forecastCongruenceOutput (R := ℤ) short u
              (fun j => Sum.elim (w j).2 (deck j)) o : ZMod N))) *
            siteFamilyFactor e k site
              (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
              (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
                basisAxisScale (basis (selected a).1) (selected a).2) =
          (((C : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun x => (u x : ZMod M))) *
            F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
              (fun i => (deck j i : ZMod M)))
              (y, allocatedFullMixedSiteValue (R := R) U basis w) := by
  let normalized := fun z => (density z : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)
  have hb := forecastDensity_normalized_bounds density C L hbound hLips
  obtain ⟨mask, coeff, hmask, hcoeff, heq, hstar⟩ :=
    exists_forecastSpatialCharacterSplit short χ M hM
  let F := forecastNormalizedResidueFactor short selected R e k site M hd coeff (normalized)
  have hRabs : ∀ a, |R (selected a).1| ≤ 1 := fun a => by
    rw [abs_of_pos (hR (selected a).1)]
    exact hR1 a
  have hF := forecastNormalizedResidueFactor_bounds short selected R e k site M hd coeff
    (normalized) hb.1 hb.2.1 he hRabs
  refine ⟨mask, F, hmask, ?_, ?_, ?_⟩
  · intro label y
    exact (hF label).1 y
  · intro label
    exact (hF label).2
  · intro u deck w y
    dsimp only [F]
    rw [forecastNormalizedResidueFactor_mixed short selected R e k site M hd U basis coeff
      (normalized) (fun j => (hR j).ne') w deck y]
    have hlabels : (fun j i => ((Sum.elim (w j).2 (deck j) i : ℤ) : ZMod M)) =
        (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
          (fun i => (deck j i : ZMod M))) := by
      funext j i
      cases i <;> rfl
    rw [hb.2.2, hstar, hlabels]
    ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastDensityPhysicalApproximation
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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

include hR hbound hLips in
theorem exists_forecastDensityBufferedTwist
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M)
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
    (coverDegree : ℕ) [NeZero coverDegree] (hcover : M ∣ coverDegree)
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
    let Lg := max ((Lfactor * max 1 Lcoord) * max 1 (M : ℝ≥0)) (4 * M)
    let Lout := Lcut * M + Lg
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ F : (∀ j, Fin (n j) ⊕ Eout j → ZMod M) →
        (X → ℝ) × (LayerSamplerAxis I n → ℝ) → ℂ,
      (∀ a, ‖mask a‖ = 1) ∧ (∀ a v, ‖F a v‖ ≤ 1) ∧
      (∀ a, LipschitzWith Lfactor (F a)) ∧
      (∀ (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (density
          ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
            forecastNormalizedActiveCoordinates short
              (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
          star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
            (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
          siteFamilyFactor e k site
            (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
            (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
              basisAxisScale (basis (selected a).1) (selected a).2) =
        (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
          F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
            (fun i => (deck j i : ZMod M)))
            (fun i => (u i : ℝ) / physicalN i, allocatedFullMixedSiteValue (R := R) U basis w)) ∧
      ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) M M Lout,
        twist.modulus = M ∧ twist.cover = M ∧
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
          (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
            forecastBufferedCoveredSiteFactor B U basis S o hb bW
              coverDegree bufferRadius hbuffer M F (fun i => (u i : ℝ) / physicalN i)
              (physicalSingleSiteValue U coverDegree poly hpoly (fun i => (u i : ℝ))) =
          2 * (((cap : ℝ) + 1 : ℝ) : ℂ) * twist.eval physicalN poly u := by
  intro Lspatial Lfactor Lcoord Lcut Lg Lout
  obtain ⟨mask, Fraw, hmask, hFraw, hFrawL, hvalue⟩ :=
    exists_forecastDensityResidueFactor (X := X)
      B U basis hR S density cap lip hbound hLips selected hR1 χ M hM e he k site hd
  let coordinateMap := fun v : (X → ℝ) × (LayerSamplerAxis I n → ℝ) =>
    (forecastNormalizedSpatialCoordinates base physicalN τ v.1, v.2)
  have hcoord : LipschitzWith Lspatial coordinateMap := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    change max (dist (forecastNormalizedSpatialCoordinates base physicalN τ v.1)
      (forecastNormalizedSpatialCoordinates base physicalN τ w.1)) (dist v.2 w.2) ≤ _
    have hleft : 8 / τ ≤ (Lspatial : ℝ) := le_max_left _ _
    have hright : (1 : ℝ) ≤ (Lspatial : ℝ) := le_max_right _ _
    apply max_le
    · have h := (forecastNormalizedSpatialCoordinates_lipschitz base physicalN hτ).dist_le_mul v.1 w.1
      change _ ≤ (8 / τ) * dist v.1 w.1 at h
      exact h.trans (mul_le_mul hleft (le_max_left _ _) dist_nonneg (NNReal.coe_nonneg _))
    · calc
        dist v.2 w.2 ≤ dist v w := le_max_right _ _
        _ = 1 * dist v w := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hright dist_nonneg
  let F := fun label => Fraw label ∘ coordinateMap
  have hFL (label) : LipschitzWith Lfactor (F label) := (hFrawL label).comp hcoord
  have hF (label) (v) : ‖F label v‖ ≤ 1 := hFraw label _
  obtain ⟨twist, hmodulus, htwistcover, htwist⟩ :=
    exists_forecast_buffered_normalized_twist_s2 B U basis S o hb bW
      coverDegree bufferRadius hbuffer M hcover hR Cinv hCinv hchart hbudget
      Cforward hforward K hK (fun a => star (mask a))
      (fun a => by rw [norm_star, hmask]) F hFL hF
  refine ⟨mask, F, hmask, hF, hFL, ?_, twist, hmodulus, htwistcover, ?_⟩
  · intro u deck w
    have hsp : forecastNormalizedSpatialCoordinates base physicalN τ
        (fun i => (u i : ℝ) / physicalN i) =
        fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8) := by
      funext a
      exact forecastNormalizedSpatialCoordinates_eval base u physicalN τ a
    dsimp only [F, Function.comp_def, coordinateMap]
    rw [hsp]
    exact hvalue u deck w _
  · intro poly hpoly u
    rw [mul_assoc, htwist physicalN poly hpoly u]
    ring

end Erdos3.VectorPolynomial

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
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

include hR hbound hLips in
theorem exists_forecastDensityBufferedPhysicalAtom_s2_oai
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M)
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
    let Lg := max ((Lfactor * max 1 Lcoord) * max 1 (M : ℝ≥0)) (4 * M)
    let Lout := Lcut * M + Lg
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) M M Lout,
      twist.modulus = M ∧ twist.cover = M ∧
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
          ((density
            ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
              forecastNormalizedActiveCoordinates short
                (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
            star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
              (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
            siteFamilyFactor e k site
              (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
              (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
                basisAxisScale (basis (selected a).1) (selected a).2)) =
          2 * (((cap : ℝ) + 1 : ℝ) : ℂ) * twist.eval physicalN poly u) ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
        allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 0 →
        twist.eval physicalN poly u = 0) := by
  intro Lspatial Lfactor Lcoord Lcut Lg Lout
  obtain ⟨mask, F, _, _, _, hvalue, twist, hmodulus, hcover, htwist⟩ :=
    exists_forecastDensityBufferedTwist (X := X)
      B U basis hR S density cap lip hbound hLips selected hR1 χ M hM e he k site hd base physicalN τ hτ
      o bW hb Cforward hforward K hK M (dvd_refl M)
      bufferRadius hbuffer Cinv hCinv hchart hbudget
  have hcut (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
      (allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
        (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) : ℂ) =
      allocatedBufferedSiteChartFactor B U basis S o hb bW M bufferRadius hbuffer
        (fun _ => 1) (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) := by
    simpa only [physicalSingleSiteValue_ambient] using
      allocatedBufferedTorusCutoff_eq_siteChart_s2 U basis o bufferRadius hbuffer
        hR Cinv hCinv hchart hbudget B S hb bW M
        (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ)))
  refine ⟨twist, hmodulus, hcover, ?_, ?_⟩
  · intro poly hpoly u w deck hdeck hquarter
    have hy : (fun j (_ : Unit) => QuotientAddGroup.mk ((M : ℝ)⁻¹ •
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)) =
        physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ)) := by
      funext j t
      cases t
      exact (physicalSingleSiteValue_eq_mk U poly hpoly M _ j).symm
    have hbuf := forecastBufferedCoveredSiteFactor_integer_deck
      B U basis S o hb bW M bufferRadius hbuffer F
      (fun i => (u i : ℝ) / physicalN i) w deck
      (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ))) hdeck hquarter
    dsimp only at hbuf
    rw [hy, ← hcut poly hpoly u] at hbuf
    rw [hvalue u deck w]
    calc
      _ = (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
          forecastBufferedCoveredSiteFactor B U basis S o hb bW M bufferRadius hbuffer M F
            (fun i => (u i : ℝ) / physicalN i)
            (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) := by
        rw [hbuf]
        ring
      _ = _ := htwist poly hpoly u
  · intro poly hpoly u hzero
    have hsite : allocatedBufferedSiteChartFactor B U basis S o hb bW M bufferRadius hbuffer
        (fun _ => 1) (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) = 0 := by
      rw [← hcut poly hpoly u, hzero, Complex.ofReal_zero]
    have hbuf := forecastBufferedCoveredSiteFactor_zero_of_cutoff_zero
      B U basis S o hb bW M bufferRadius hbuffer M F
      (fun i => (u i : ℝ) / physicalN i)
      (physicalSingleSiteValue U M poly hpoly (fun i => (u i : ℝ))) hsite
    have ht := htwist poly hpoly u
    rw [hbuf, mul_zero] at ht
    have hH : (2 * (((cap : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (2 : ℝ) * ((cap : ℝ) + 1) ≠ 0 by positivity)
    exact (mul_eq_zero.mp ht.symm).resolve_left hH

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} : type_of% @OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedPhysicalAtom_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} := @OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedPhysicalAtom_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
