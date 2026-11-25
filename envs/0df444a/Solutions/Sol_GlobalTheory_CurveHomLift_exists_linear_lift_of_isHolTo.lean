-- Prove2me | solution 1 for GlobalTheory.CurveHomLift.exists_linear_lift_of_isHolTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:55:28.80999+00:00
-- url     : https://prove2.me/submissions/4ae0bc38-cb5e-499f-9bc3-c3c47a97be0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVector
import Theorems.Thm_Formalism_L2_Pj_ex_add
import Theorems.Thm_GlobalTheory_ExpUniqFamily_isHolTo_ex
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_fibPt
import Theorems.Thm_GlobalTheory_LocalLift_exists_local_lift
import Theorems.Thm_GlobalTheory_UniformLift_existsUnique_linearMap_lift_of_germ
import Theorems.Thm_GlobalTheory_UniformLift_fibPt_fst
import Theorems.Thm_GlobalTheory_UniformLift_fibPt_injective
import Theorems.Thm_GlobalTheory_UniformLift_fibPt_snd
import Theorems.Thm_GlobalTheory_UniformLift_map_zero_eq_one
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_isDerivAt0_fibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CurveHomLift
open UniformLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.CurveHomLift
theorem _root_.solution (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {m : ℕ} (e : (Fin m → ℂ) → (Over.mk (F.u i P) ⟶ Xo.univ.t.G))
    (he : ∀ z w, e (z + w) = e z * e w) (hol : IsHolTo Set.univ fun z => (e z).left) :
    ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, F.ex i P (L z) = e z := by
  have hsm : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  have hsm' : Smooth (pullback.snd Xo.univ.t.G.hom (F.u i P)) := inferInstance
  have hol' := ExpUniqFamily.isHolTo_ex F i P hP
  have he' := F.ex_add i P hP
  have hd := isDerivAt0_fibre _ Xo.univ.t.G (F.u i P) g (F.ex i P) _ _ _ (fun z => fibPt _ (F.ex i P z))
    (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' (F.ex_diff i P hP)
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd Xo.univ.t.G.hom (F.u i P)) m g
    (fun z => fibPt _ (e z)) (fun z => fibPt _ (F.ex i P z)) hsm'
    (fun z => fibPt_snd _ _) (fun z => fibPt_snd _ _)
    (HolFibre.isHolTo_fibPt isOpen_univ _ _ e hol) (HolFibre.isHolTo_fibPt isOpen_univ _ _ _ hol') hd
    (by simp only [map_zero_eq_one e he, map_zero_eq_one _ he'])
  have hker : ((toAddHom (F.ex i P) he').ker : Set (Fin g → ℂ)) = P.range := Set.ext fun z => F.ex_ker i P hP z
  exact (existsUnique_linearMap_lift_of_germ (ex := toAddHom e he) (ex' := toAddHom (F.ex i P) he')
    (hker ▸ isDiscrete_iff_discreteTopology.2 hP.2.2.1) hka.differentiableAt k0
    (hk.mono fun z hz => fibPt_injective _ hz)).exists
end GlobalTheory.CurveHomLift
