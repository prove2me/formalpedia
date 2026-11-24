-- Prove2me | solution 1 for GlobalTheory.BaseRing.finiteType_RZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:22.097655+00:00
-- url     : https://prove2.me/submissions/ea966580-5a11-4f40-ac35-91d35ceac60d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmModelCoefficientSubringDedekindCompatibleEmbed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BaseRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.BaseRing
theorem _root_.solution (H : Host E) (S A : ℕ) : Algebra.FiniteType ℤ (RZ H S A) := by
  classical
  have h : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).FG :=
    Subalgebra.fg_def.mpr ⟨_, Set.toFinite _, rfl⟩
  have h2 := (Subalgebra.fg_iff_finiteType _).mp h
  have h3 : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).toSubring = RZ H S A := by
    rw [Algebra.adjoin_int]; rfl
  exact h2.equiv (RingEquiv.subringCongr h3).toIntAlgEquiv
end GlobalTheory.BaseRing
