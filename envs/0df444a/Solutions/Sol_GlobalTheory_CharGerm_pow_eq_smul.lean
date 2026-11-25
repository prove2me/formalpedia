-- Prove2me | solution 1 for GlobalTheory.CharGerm.pow_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:36:14.006536+00:00
-- url     : https://prove2.me/submissions/53b6e810-041d-4ae7-b557-e545ff2c7cc5

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_GlobalTheory_CharGerm_mul_eq_add
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
      ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)
include h0 hnat hinj hsurj
namespace GlobalTheory.CharGerm
theorem _root_.solution {S : Type} [CommRing S] [Algebra R₀ S] {I : Ideal S} (hI : I ^ 2 = ⊥)
    {a : Fin g → S} (ha : ∀ i, a i ∈ I) (n : ℕ) : x S a ^ n = x S (fun i => (n : S) * a i) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact (h0 S).symm
  | succ n ih =>
    rw [pow_succ, ih, mul_eq_add h0 hnat hinj hsurj hI (fun i => Ideal.mul_mem_left _ _ (ha i)) ha]
    congr 1
    funext i
    simp [add_mul]
end GlobalTheory.CharGerm
