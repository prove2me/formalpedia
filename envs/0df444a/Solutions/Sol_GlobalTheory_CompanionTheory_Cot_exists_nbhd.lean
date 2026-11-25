-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cot.exists_nbhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:05.168612+00:00
-- url     : https://prove2.me/submissions/7074504b-eb6a-4c14-a1d0-c18529c80abd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffineStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMapStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreenessStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExistsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLocalChartAtPrimeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsNbhd
import Theorems.Thm_GlobalTheory_CompanionTheory_Cot_spMap_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_Cot_spMap_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Cot_spMap_id
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_spMap_inj
import Theorems.Thm_GlobalTheory_T_ideal_square_le_kernel_of_square_zero_map
import Theorems.Thm_GlobalTheory_T_square_zero_neighbourhood_affine
import Theorems.Thm_GlobalTheory_T_square_zero_neighbourhood_product_zero
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cot
namespace GlobalTheory.CompanionTheory.Cot
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∃ (P : Type) (_ : CommRing P) (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R ∧ (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) ∧ j ≫ s = spMap α ∧ spMap ε ≫ j = e ∧ Mono j ∧ ∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y := by
  intro R _ X s e he
  have : IsImmersion (e ≫ s) := by rw [he]; infer_instance
  have : IsImmersion e := IsImmersion.of_comp e s
  let U := e.coborderRange
  let e' : Sp R ⟶ U := e.liftCoborder
  have he' : e' ≫ U.ι = e := e.liftCoborder_ι
  let t : (U : Scheme.{0}) ⟶ Sp R := U.ι ≫ s
  have het : e' ≫ t = 𝟙 _ := by simp only [t]; rw [← Category.assoc, he', he]
  have hE : IsAffine (e'.ker ^ 2).subscheme := GlobalTheory.T.square_zero_neighbourhood_affine R U t e' het
  let c := (e'.ker ^ 2).subschemeι
  have hle : c.ker ≤ e'.ker := by
    simp only [c, Scheme.IdealSheafData.ker_subschemeι]
    exact pow_le_of_le_one zero_le le_top two_ne_zero
  let i' : Sp R ⟶ (e'.ker ^ 2).subscheme := IsClosedImmersion.lift c e' hle
  have hi' : i' ≫ c = e' := IsClosedImmersion.lift_fac _ _ _
  let E := (e'.ker ^ 2).subscheme
  let P : Type := Γ(E, ⊤)
  let iso : E ≅ Sp P := E.isoSpec
  let j : Sp P ⟶ X := iso.inv ≫ c ≫ U.ι
  let α : R →+* P := (Spec.preimage (iso.inv ≫ c ≫ t)).hom
  let ε : P →+* R := (Spec.preimage (i' ≫ iso.hom)).hom
  have hα : spMap α = iso.inv ≫ c ≫ t := Spec.map_preimage _
  have hε : spMap ε = i' ≫ iso.hom := Spec.map_preimage _
  have hjs : j ≫ s = spMap α := by simp [j, hα, t]
  have hεj : spMap ε ≫ j = e := by
    simp only [hε, j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', he']
  refine ⟨P, inferInstance, α, ε, j, ?_, ?_, hjs, hεj, inferInstance, ?_⟩
  · apply spMap_inj
    rw [spMap_comp, hε, hα, spMap_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', het]
  · have h0 : CommRingCat.ofHom ε = i'.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
      have h1 : (spMap ε).appTop = (Scheme.ΓSpecIso (.of P)).hom ≫ i'.appTop := by
        rw [hε, Scheme.Hom.comp_appTop]
        simp only [iso, Scheme.isoSpec, asIso_hom]
        exact congrArg (fun f ↦ f ≫ i'.appTop) (Scheme.toSpecΓ_appTop E)
      have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ε)
      rw [h1, Category.assoc] at h2
      exact ((cancel_epi _).1 h2).symm
    have hk : ∀ a : P, ε a = 0 → i'.appTop a = 0 := fun a ha ↦ by
      have h3 : (Scheme.ΓSpecIso (.of R)).hom (i'.appTop a) = 0 := by
        have := congrArg (fun f ↦ f.hom a) h0
        simpa [ha] using this.symm
      exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1).1 h3
    intro a b ha hb
    exact GlobalTheory.T.square_zero_neighbourhood_product_zero R U e' i' hi' a b (hk a ha) (hk b hb)
  · intro Q B _ _ q ρ y hq hsq hy
    have hsurj : Function.Surjective (spMap q) := by
      intro x
      have hx : x ∈ Set.range (PrimeSpectrum.comap q) := by
        rw [range_comap_of_surjective _ _ hq]
        intro a ha
        have : a * a = 0 := hsq a a ha ha
        exact x.2.mem_or_mem (by simp [this] : a * a ∈ x.asIdeal) |>.elim id id
      exact hx
    have hr : Set.range y ⊆ Set.range U.ι := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨x', rfl⟩ := hsurj x
      have h1 : y (spMap q x') = e (spMap ρ x') := by
        rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
      rw [h1, ← he', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    let y' : Sp Q ⟶ U := IsOpenImmersion.lift U.ι y hr
    have hy' : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
    have hy2 : spMap q ≫ y' = spMap ρ ≫ e' := by
      rw [← cancel_mono U.ι, Category.assoc, hy', hy, Category.assoc, he']
    have hk : c.ker ≤ y'.ker := by
      simp only [c, Scheme.IdealSheafData.ker_subschemeι]
      exact GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map R Q B U e' q ρ y' hq hsq hy2
    let w : Sp Q ⟶ E := IsClosedImmersion.lift c y' hk
    have hw : w ≫ c = y' := IsClosedImmersion.lift_fac _ _ _
    refine ⟨(Spec.preimage (w ≫ iso.hom)).hom, ?_⟩
    have : spMap (Spec.preimage (w ≫ iso.hom)).hom = w ≫ iso.hom := Spec.map_preimage _
    rw [this]
    simp only [j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc w, hw, hy']
end GlobalTheory.CompanionTheory.Cot
