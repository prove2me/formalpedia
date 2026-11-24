-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.seesaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:31.368082+00:00
-- url     : https://prove2.me/submissions/808eb1e7-475c-44c7-a46a-b680bd88f0f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_exists_kernel_vector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_mem_of_isUnit
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_mem_basicOpen_cst
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_loc_smul
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_exists_mem
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_loc_comp
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_triv_of_loc
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_loc_of_triv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ (r : R) (I : Ideal R), g₀ r ≠ 0 ∧ I.FG ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  rintro R _ X f M hM ⟨P⟩ hcl hsurj K _ g₀ X₀ π₀ f₀ h₀ hb ht
  obtain ⟨v, hv, hu, hline⟩ := loc_of_triv P h₀ hM ht
  let z : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have unit_cst : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
      ∀ (c : R') (w : Fin P.a → R'), (∀ i, IsUnit (loc P π f' (c • w) i)) → IsUnit c := by
    intro R' _ g X' π f' h c w H
    by_contra hc
    obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
    have : Surjective f' := MorphismProperty.of_isPullback h hsurj
    obtain ⟨y, hy⟩ := f'.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have h₁ := H i
    rw [loc_smul] at h₁
    have h₂ := (mem_basicOpen_cst f' _ c hi).1 (mem_of_isUnit (isUnit_of_mul_isUnit_left h₁) hi)
    rw [hy] at h₂
    exact h₂ hcm
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (unit_cst K g₀ X₀ π₀ f₀ h₀ 0 0 (by rwa [smul_zero]))
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline hb.2)
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P v₀ i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hp : Spec.map (CommRingCat.ofHom g₀) z ∈ (f '' (G : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₀ x z hfx
    obtain ⟨i, hi⟩ := exists_mem P (π₀ y)
    obtain ⟨c, hc⟩ := hker K g₀ hδ.isUnit v hv
    have h₁ := hu i
    rw [hc, loc_smul, loc_comp P h₀] at h₁
    have h₂ := mem_of_isUnit (isUnit_of_mul_isUnit_right h₁) (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩)
  obtain ⟨_, ⟨r₁, rfl⟩, hr₁, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hZ.isOpen_compl
  have hr₁' : g₀ r₁ ≠ 0 := hr₁
  refine ⟨δ * r₁, Ideal.span (Set.range (P.D₀.mulVec v₀)), by rw [map_mul]; exact mul_ne_zero hδ hr₁',
    Submodule.fg_span (Set.finite_range _), fun R' _ g X' π f' h hr => ?_⟩
  rw [map_mul] at hr
  have hI : Ideal.span (Set.range (P.D₀.mulVec v₀)) ≤ RingHom.ker g ↔ (P.D₀.map g).mulVec (g ∘ v₀) = 0 := by
    rw [Ideal.span_le, Set.range_subset_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [← RingHom.map_mulVec]
    rfl
  rw [hI]
  constructor
  · intro H
    obtain ⟨w, hw, hwu, -⟩ := loc_of_triv P h hM H
    obtain ⟨c, rfl⟩ := hker R' g (isUnit_of_mul_isUnit_left hr) w hw
    rw [Matrix.mulVec_smul] at hw
    exact ((unit_cst R' g X' π f' h c _ hwu).smul_eq_zero).1 hw
  · intro H
    refine triv_of_loc P h _ H fun y => ?_
    have hy : π y ∈ G := by
      by_contra hy
      have e : f (π y) = Spec.map (CommRingCat.ofHom g) (f' y) := congrArg (fun q => q y) h.w
      refine hsub (a := f (π y)) ?_ ⟨π y, hy, rfl⟩
      rw [e]
      change g r₁ ∉ (f' y).asIdeal
      exact fun hm => (f' y).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (isUnit_of_mul_isUnit_right hr))
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    rw [loc_comp P h, ← Scheme.preimage_basicOpen]
    exact hi
end GlobalTheory.AbLaw.Seesaw
