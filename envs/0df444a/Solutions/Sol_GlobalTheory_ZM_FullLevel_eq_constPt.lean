-- Prove2me | solution 1 for GlobalTheory.ZM.FullLevel.eq_constPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:07.695966+00:00
-- url     : https://prove2.me/submissions/e071ed8e-fb88-4469-a2cd-934cacb217e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinimalAndDimLe
import Theorems.Thm_GlobalTheory_ZM_FullLevel_charZero_of_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM.FullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem isNilpotent_ker_fstHom_dualNumber {K : Type} [Field K] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hr hs
  rw [Ideal.mem_bot]
  ext <;> simp [hr, hs]
end GlobalTheory.ZM.FullLevel
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.FullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ZM.FullLevel
namespace _root_.GlobalTheory.ZM.FullLevel
theorem _root_.solution {k K : Type} [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K]
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) : x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt x := by
  have hK : CharZero K :=
    _root_.GlobalTheory.ZM.FullLevel.charZero_of_hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ x)
  haveI : Algebra.IsSeparable ℚ k := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified ℚ k := Algebra.FormallyUnramified.of_isSeparable ℚ k
  obtain ⟨φ, rfl⟩ : ∃ φ : k →+* DualNumber K, x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ :=
    ⟨(Spec.preimage x).hom, by simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]⟩
  let ψ : k →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)
  have hψ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ψ, ← Spec.map_comp]; rfl
  rw [hψ]
  congr 1
  have key := Algebra.FormallyUnramified.ext (R := ℚ) (A := k) (B := DualNumber K)
    (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) isNilpotent_ker_fstHom_dualNumber
    (g₁ := φ.toRatAlgHom) (g₂ := ψ.toRatAlgHom) ?_
  · exact congrArg AlgHom.toRingHom key
  · intro a
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp [ψ, TrivSqZeroExt.algebraMap_eq_inl]
end _root_.GlobalTheory.ZM.FullLevel
end GlobalTheory.ZM.FullLevel
