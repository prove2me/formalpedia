-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:38.943564+00:00
-- url     : https://prove2.me/submissions/a7245392-0684-4d09-8b8d-f394ec2c83a4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_GlobalTheory_IndivisibleSection_exists_generator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndivisibleSection
section Calc
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
end Calc
section Deg
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
private theorem scal_mul_divisor {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) (a b : R) :
    scal p (a * b) = scal p a * scal p b := by
  unfold scal
  rw [map_mul, map_mul]
private theorem resTop_mul' {Y : Scheme.{0}} (W : Y.Opens) (x y : Γ(Y, ⊤)) :
    resTop W (x * y) = resTop W x * resTop W y := by
  unfold resTop
  exact map_mul _ _ _
private theorem scal_one_rings_of_integers {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) :
    scal p (1 : R) = 1 := by
  unfold scal
  rw [map_one, map_one]
private theorem resTop_one {Y : Scheme.{0}} (W : Y.Opens) : resTop W (1 : Γ(Y, ⊤)) = 1 := by
  unfold resTop
  exact map_one _
end Deg
end GlobalTheory.IndivisibleSection
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndivisibleSection
namespace GlobalTheory.IndivisibleSection
theorem _root_.solution : SecBaseChangeSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (g : D.toPre.SecB 1 0), (¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ g g') → SecBGenerates (D := D) 1 0 g := by
  intro hS V _ _ _ ϖ hϖ D g hg
  obtain ⟨b, hb⟩ := exists_generator D.toPre hS
  obtain ⟨a, ha, -⟩ := hb g
  have hmul : ∀ (x y : V) (s t w : D.toPre.SecB 1 0), SecIsMul D.toPre.P.A.hom x s t →
      SecIsMul D.toPre.P.A.hom y t w → SecIsMul D.toPre.P.A.hom (x * y) s w := by
    intro x y s t w h1 h2
    unfold SecIsMul at h1 h2 ⊢
    intro j
    rw [h1 j, h2 j, scal_mul_divisor, resTop_mul', _root_.mul_assoc]
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    have hinv : SecIsMul D.toPre.P.A.hom (↑u⁻¹ : V) b g := by
      unfold SecIsMul at ha ⊢
      intro j
      rw [ha j, ← _root_.mul_assoc, ← resTop_mul', ← scal_mul_divisor, Units.inv_mul, scal_one_rings_of_integers, resTop_one,
        _root_.one_mul]
    unfold SecBGenerates
    intro s
    obtain ⟨c, hc, hcu⟩ := hb s
    refine ⟨c * ↑u⁻¹, hmul _ _ _ _ _ hc hinv, fun d hd => ?_⟩
    have hdu := hcu (d * u) (hmul _ _ _ _ _ hd ha)
    rw [← hdu, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  · exfalso
    apply hg
    have hmax : a ∈ maximalIdeal V := (IsLocalRing.mem_maximalIdeal a).mpr hu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton'] at hmax
    obtain ⟨a', rfl⟩ := hmax
    refine ⟨smulSec (scal D.toPre.P.A.hom a') b, ?_⟩
    unfold SecIsMul at ha ⊢
    intro j
    rw [ha j, _root_.mul_comm a' ϖ, scal_mul_divisor, resTop_mul', _root_.mul_assoc]
    rfl
end GlobalTheory.IndivisibleSection
