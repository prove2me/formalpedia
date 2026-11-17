-- Prove2me | solution 1 for N25.canonicalProjScalarSection25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:28.579213+00:00
-- url     : https://prove2.me/submissions/fe948ee3-f599-4ecc-b066-235c0c5cf062

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart

/-! Structural scalar compatibility on every homogeneous principal open. -/
noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable (K : Type u) [Field K]

/-- The homogeneous-localization coefficient map is the restriction of the selected structure map. -/
theorem _root_.solution (f : CanonicalConeRing25 K) {m : ℕ}
    (hf : f ∈ canonicalConePiece25 K m) (hm : 0 < m) :
    CommRingCat.ofHom ((fromZeroRingHom (canonicalConePiece25 K) (Submonoid.powers f)).comp
      (algebraMap K (canonicalConePiece25 K 0))) ≫
        Proj.awayToSection (canonicalConePiece25 K) f =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (canonicalProjectiveCurveToSpec25 K).appLE ⊤ (Proj.basicOpen (canonicalConePiece25 K) f) le_top := by
  let U := Proj.basicOpen (canonicalConePiece25 K) f
  let α := CommRingCat.ofHom
    ((fromZeroRingHom (canonicalConePiece25 K) (Submonoid.powers f)).comp
      (algebraMap K (canonicalConePiece25 K 0)))
  let c := canonicalProjectiveCurveToSpec25 K
  let e := Proj.basicOpenIsoSpec (canonicalConePiece25 K) f hf hm
  have hU : IsAffineOpen U := Proj.isAffineOpen_basicOpen (canonicalConePiece25 K) f hf hm
  letI : IsIso U.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  have hstruct : Proj.awayι (canonicalConePiece25 K) f hf hm ≫ c = Spec.map α := by
    dsimp only [c, canonicalProjectiveCurveToSpec25]
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have he : U.toSpecΓ ≫ Spec.map (Proj.awayToSection (canonicalConePiece25 K) f) = e.hom := by
    rw [Proj.basicOpenIsoSpec_hom]
    rfl
  apply Spec.map_injective
  apply (cancel_epi U.toSpecΓ).mp
  calc
    U.toSpecΓ ≫ Spec.map (α ≫ Proj.awayToSection (canonicalConePiece25 K) f) =
        U.ι ≫ c := by
      rw [Spec.map_comp, ← Category.assoc, he, ← hstruct]
      dsimp only [e, Proj.awayι]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl
    _ = U.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        c.appLE ⊤ U le_top) := by
      have hUV : U ≤ c ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := by simp
      have ht := Scheme.Opens.toSpecΓ_SpecMap_appLE c ⊤ U hUV
      have ht' := congrArg
        (fun g => g ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv) ht
      simp only [Scheme.Opens.toSpecΓ_top, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id] at ht'
      rw [Scheme.Hom.resLE_comp_ι] at ht'
      simpa only [Spec.map_comp, Category.assoc] using ht'.symm

end N25
