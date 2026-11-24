-- Prove2me | solution 1 for GlobalTheory.TorusToProper.units_family_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:56.551438+00:00
-- url     : https://prove2.me/submissions/419987c5-1f1b-47c1-ab1e-d1faaf80367e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Theorems.Thm_GlobalTheory_TorusToProper_spm_comp
import Theorems.Thm_GlobalTheory_TorusToProper_spm_id
import Theorems.Thm_GlobalTheory_TorusToProper_point_ext
import Theorems.Thm_GlobalTheory_TorusToProper_point_extend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
open PowerSeries
namespace GlobalTheory.TorusToProper
theorem _root_.solution {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsProper B.hom]
    (Φ : ∀ (R : Type) [CommRing R] [Algebra K R], Rˣ →* (sp K R ⟶ B))
    (hΦ : ∀ (R R' : Type) [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (g : R →ₐ[K] R')
      (x : Rˣ), Φ R' (Units.map (g : R →* R') x) = spm g ≫ Φ R x)
    (L : Type) [Field L] [Algebra K L] (x : Lˣ) : Φ L x = 1 := by
  let F := FractionRing L⟦X⟧
  let j : L⟦X⟧ →ₐ[K] F := IsScalarTower.toAlgHom K L⟦X⟧ F
  have hj : Function.Injective j := IsFractionRing.injective L⟦X⟧ F
  let σ : L⟦X⟧ →ₐ[K] L⟦X⟧ := (rescaleAlgHom (x : L)).restrictScalars K
  have hσ : ∀ a, σ a = rescale (x : L) a := fun a =>
    RingHom.congr_fun (coe_rescaleAlgHom (x : L)) a
  have hσi : Function.Injective (j.comp σ) := by
    intro a b hab
    have h1 : σ a = σ b := hj hab
    rw [hσ, hσ] at h1
    exact rescale_injective x.ne_zero h1
  let τ : F →ₐ[K] F := IsFractionRing.liftAlgHom (g := j.comp σ) hσi
  have hτ : τ.comp j = j.comp σ := by
    ext a
    simp [τ, j]
  let c : L →ₐ[K] L⟦X⟧ := IsScalarTower.toAlgHom K L L⟦X⟧
  let ev : L⟦X⟧ →ₐ[K] L := { toRingHom := constantCoeff, commutes' := fun r => by simp [PowerSeries.algebraMap_apply] }
  have hev : ∀ a, ev a = constantCoeff a := fun _ => rfl
  have h1 : ev.comp σ = ev := by
    ext a
    rw [AlgHom.comp_apply, hσ, hev, hev, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
    simp
  have h2 : ev.comp c = AlgHom.id K L := by
    ext a
    simp [hev, c, PowerSeries.algebraMap_apply]
  have hX : j X ≠ 0 := fun h => X_ne_zero (hj (h.trans (map_zero j).symm))
  let u : Fˣ := Units.mk0 (j X) hX
  obtain ⟨b, hb⟩ := point_extend (K := K) (V := L⟦X⟧) (Φ F u)
  have hu : Units.map (τ : F →* F) u = Units.map ((j.comp c : L →ₐ[K] F) : L →* F) x * u := by
    ext
    have := congrArg (fun g : L⟦X⟧ →ₐ[K] F => g X) hτ
    simp only [AlgHom.comp_apply, hσ, rescale_X, map_mul] at this
    simpa [u, c, PowerSeries.algebraMap_apply] using this
  have key : spm σ ≫ b = (spm c ≫ Φ L x) * b := by
    apply point_ext j hj
    rw [← Category.assoc, spm_comp, ← hτ, ← spm_comp, Category.assoc, MonObj.comp_mul, hb, ← hΦ, hu,
      map_mul, hΦ, ← Category.assoc, spm_comp]
  have k2 := congrArg (fun t => spm ev ≫ t) key
  simp only [MonObj.comp_mul, ← Category.assoc, spm_comp, h1, h2, spm_id, Category.id_comp] at k2
  exact right_eq_mul.1 k2
end GlobalTheory.TorusToProper
