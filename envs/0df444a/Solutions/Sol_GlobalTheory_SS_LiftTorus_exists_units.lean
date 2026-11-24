-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:07.051265+00:00
-- url     : https://prove2.me/submissions/4737dc30-a170-48b5-a40e-a3d3e2fb7c4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LiftTorus
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C : Type} [CommRing A] [CommRing C]
  {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X}
namespace GlobalTheory.SS.LiftTorus
theorem _root_.solution [Subsingleton (CommRing.Pic A)] [Module.Free ℤ X] (hα : α.FaithfullyFlat)
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) :
    ∃ u : Multiplicative X →* Cˣ, ∀ x,
      ρ (u (Multiplicative.ofAdd x)).val =
        AddMonoidAlgebra.single x (u (Multiplicative.ofAdd x)).val := by
  choose v hv using exists_unit hα h
  let b := Module.Free.chooseBasis ℤ X
  let l : X →ₗ[ℤ] Additive Cˣ := b.constr ℤ fun j => Additive.ofMul (v (b j))
  let u : Multiplicative X →* Cˣ := AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom
  let w₁ : Multiplicative X →* (AddMonoidAlgebra C X)ˣ := (Units.map ρ.toMonoidHom).comp u
  let w₂ : Multiplicative X →* (AddMonoidAlgebra C X)ˣ :=
    univ X C * (Units.map (cst X C).toMonoidHom).comp u
  have hw₂ : ∀ x, (w₂ (Multiplicative.ofAdd x)).val =
      AddMonoidAlgebra.single x (u (Multiplicative.ofAdd x)).val := fun x => by
    change AddMonoidAlgebra.single x 1 * AddMonoidAlgebra.single 0 _ = _
    rw [AddMonoidAlgebra.single_mul_single, add_zero, _root_.one_mul]
  have hw : (MonoidHom.toAdditiveRight w₁).toIntLinearMap =
      (MonoidHom.toAdditiveRight w₂).toIntLinearMap := by
    refine b.ext fun j => ?_
    have hu : u (Multiplicative.ofAdd (b j)) = v (b j) :=
      congrArg Additive.toMul (b.constr_basis ℤ (fun j => Additive.ofMul (v (b j))) j)
    refine congrArg Additive.ofMul (Units.ext ?_)
    refine Eq.trans ?_ (hw₂ (b j)).symm
    change ρ (u (Multiplicative.ofAdd (b j))).val = _
    rw [hu, hv]
  refine ⟨u, fun x => Eq.trans ?_ (hw₂ x)⟩
  exact congrArg (fun z => (Additive.toMul z).val) (LinearMap.congr_fun hw x)
end GlobalTheory.SS.LiftTorus
