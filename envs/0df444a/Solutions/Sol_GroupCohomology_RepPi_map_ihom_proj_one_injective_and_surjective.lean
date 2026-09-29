-- Prove2me | solution 1 for GroupCohomology.RepPi.map_ihom_proj_one_injective_and_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/74aadae4-4d24-5735-bfb5-7ef81524e5e4

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective

set_option autoImplicit false
open CategoryTheory

namespace ShapiroJ2
open groupCohomology

universe u
variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (X : ι → Rep.{u} k G) (R : Rep.{u} k G)

local notation "J" => GroupCohomology.RepPi.obj X

abbrev lin {Y : Rep.{u} k G} (f : (ihom R).obj Y) : R →ₗ[k] Y := f

set_option backward.isDefEq.respectTransparency false in
lemma ihom_ρ_apply {Y : Rep.{u} k G} (g : G) (f : (ihom R).obj Y) (r : R) :
    lin R (((ihom R).obj Y).ρ g f) r = Y.ρ g (lin R f (R.ρ g⁻¹ r)) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma ihom_map_hom_apply {Y Z : Rep.{u} k G} (φ : Y ⟶ Z) (f : (ihom R).obj Y) (r : R) :
    lin R (((ihom R).map φ).hom f) r = φ.hom (lin R f r) := rfl

abbrev piLin (f : ∀ i, (ihom R).obj (X i)) : (ihom R).obj J :=
  show R →ₗ[k] ((i : ι) → X i) from LinearMap.pi fun i => lin R (f i)

lemma piLin_apply (f : ∀ i, (ihom R).obj (X i)) (r : R) (i : ι) : lin R (piLin X R f) r i = lin R (f i) r := rfl

lemma proj_piLin (f : ∀ i, (ihom R).obj (X i)) (i : ι) :
    ((ihom R).map (GroupCohomology.RepPi.proj X i)).hom (piLin X R f) = f i := by
  apply LinearMap.ext
  intro r
  rfl

lemma ρ_piLin (g : G) (f : ∀ i, (ihom R).obj (X i)) :
    ((ihom R).obj J).ρ g (piLin X R f) = piLin X R (fun i => ((ihom R).obj (X i)).ρ g (f i)) := by
  apply LinearMap.ext
  intro r
  funext i
  rw [ihom_ρ_apply]
  change (X i).ρ g (lin R (piLin X R f) (R.ρ g⁻¹ r) i) = lin R (((ihom R).obj (X i)).ρ g (f i)) r
  rw [ihom_ρ_apply]
  rfl

noncomputable def piCocycle (z : ∀ i, cocycles₁ ((ihom R).obj (X i))) : cocycles₁ ((ihom R).obj J) :=
  ⟨fun g => piLin X R (fun i => z i g), (mem_cocycles₁_iff _).2 fun g h => by
    rw [ρ_piLin]
    apply LinearMap.ext; intro r; funext i
    change lin R (z i (g * h)) r = lin R (((ihom R).obj (X i)).ρ g (z i h)) r + lin R (z i g) r
    rw [(mem_cocycles₁_iff (z i)).1 (z i).2 g h]
    rfl⟩

lemma mapCocycles₁_proj_piCocycle (z : ∀ i, cocycles₁ ((ihom R).obj (X i))) (i : ι) :
    mapCocycles₁ (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) (piCocycle X R z) = z i := by
  apply Subtype.ext
  funext g
  rw [cocycles₁.val_eq_coe, coe_mapCocycles₁]
  change ((ihom R).map (GroupCohomology.RepPi.proj X i)).hom (piLin X R (fun i => z i g)) = _
  rw [proj_piLin]
  rfl

theorem surj (y : ∀ i, groupCohomology ((ihom R).obj (X i)) 1) :
    ∃ x : groupCohomology ((ihom R).obj J) 1,
      ∀ i, (map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = y i := by
  have hs : ∀ i, ∃ z : cocycles₁ ((ihom R).obj (X i)), H1π _ z = y i := fun i =>
    (ModuleCat.epi_iff_surjective (H1π ((ihom R).obj (X i)))).1 inferInstance (y i)
  choose z hz using hs
  refine ⟨H1π _ (piCocycle X R z), fun i => ?_⟩
  have := H1π_comp_map_apply (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) (piCocycle X R z)
  rw [mapCocycles₁_proj_piCocycle, hz] at this
  exact this

theorem inj (x : groupCohomology ((ihom R).obj J) 1)
    (hx : ∀ i, (map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = 0) : x = 0 := by
  induction x using H1_induction_on with | @h z =>
  have hc : ∀ i, ∃ y : (ihom R).obj (X i), (d₀₁ _).hom y =
      ⇑(mapCocycles₁ (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) z) := fun i => by
    have e := H1π_comp_map_apply (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) z
    have h : H1π _ (mapCocycles₁ (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) z) = 0 :=
      e.symm.trans (hx i)
    rw [H1π_eq_zero_iff] at h
    exact h
  choose y hy using hc
  rw [H1π_eq_zero_iff]
  refine ⟨piLin X R y, ?_⟩
  funext g
  erw [d₀₁_hom_apply]
  rw [ρ_piLin]
  change piLin X R (fun i => ((ihom R).obj (X i)).ρ g (y i)) - piLin X R y = lin R (z g)
  apply LinearMap.ext; intro r; funext i
  have h1 := congrFun (hy i) g
  erw [d₀₁_hom_apply, coe_mapCocycles₁] at h1
  have h2 := congrArg (fun f => lin R f r) h1
  exact h2

end ShapiroJ2

theorem solution
    {G : Type} [Group G] {ι : Type} [Finite ι] (X : ι → Rep ℤ G) (R : Rep ℤ G) :
    (∀ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
        (∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = 0) → x = 0) ∧
    (∀ y : ∀ i, groupCohomology ((ihom R).obj (X i)) 1,
        ∃ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
          ∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = y i) :=
  ⟨ShapiroJ2.inj X R, ShapiroJ2.surj X R⟩

end S_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective
end P2MW
export P2MW.S_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective (solution)
