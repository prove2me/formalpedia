-- Prove2me | solution 1 for GlobalTheory.GenExtendNormal.mem_range_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:46.476994+00:00
-- url     : https://prove2.me/submissions/bcd31918-9306-4570-a871-abcfb250c51d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_GlobalTheory_GenExtendNormal_coheight_apply_le_one
import Theorems.Thm_GlobalTheory_GenExtendNormal_mem_range_of_preimmersion
import Theorems.Thm_GlobalTheory_GenExtendNormal_exists_gen_germ
import Theorems.Thm_GlobalTheory_DvrModel_wchart_comp
import Theorems.Thm_GlobalTheory_PrimeSection_isDiscreteValuationRing_stalk
import Theorems.Thm_GlobalTheory_genericPoint_mem_opens
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendNormal
open GlobalTheory.DvrModel
namespace GlobalTheory.GenExtendNormal
theorem _root_.solution {S U H HU X : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S]
    [GlobalTheory.IsNormalScheme S] [Nonempty U] [IsIntegral H] {j : U ⟶ S} [IsOpenImmersion j] {p : H ⟶ S}
    {e : S ⟶ H} {jH : HU ⟶ H} {pU : HU ⟶ U} {eU : U ⟶ HU} [Smooth p] [GeometricallyIntegral p]
    (he : e ≫ p = 𝟙 _) (hP : IsPullback jH pU p j) (heU : eU ≫ jH = j ≫ e) {L : LB X}
    (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (H ⟶ X)} {ε : I → ℤ}
    {t : LB.Gen (LB.LinComb L (fun i ↦ jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i ↦ e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (x : H) (hx : Order.coheight x = 1) (hxU : p x ∉ Set.range j) (a : I → L.ι)
    (hxa : x ∈ LB.wchart L φ a) (A : H.Opens) [Nonempty A] (τ : Γ(H, A)ˣ)
    (hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z), jH (r z) ∈ A →
      gm (r ≫ jH) z A τ = gm r z (LB.wchart L (fun i ↦ jH ≫ φ i) a) (t.s a)) :
    H.germToFunctionField A τ.val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range ∧
    H.germToFunctionField A (τ⁻¹).val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range := by
  have hη : genericPoint S ∈ Set.range j := by
    have : Nonempty j.opensRange := ⟨⟨j (Nonempty.some inferInstance), _, rfl⟩⟩
    exact genericPoint_mem_opens j.opensRange
  have h1 : Order.coheight (p x) = 1 := by
    refine le_antisymm (coheight_apply_le_one p (Flat.generalizingMap p) x hx.le) ?_
    rw [Order.one_le_iff_ne_zero, Order.coheight_ne_zero]
    intro hm
    have h₁ : genericPoint S ⤳ p x := (genericPoint_spec S).specializes trivial
    exact hxU (Specializes.mem_open (hm (show p x ≤ genericPoint S from h₁))
      j.isOpenEmbedding.isOpen_range hη)
  have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h1
  let V : Type := S.presheaf.stalk (p x)
  let K : Type := S.functionField
  let v : Spec (CommRingCat.of V) ⟶ S := S.fromSpecStalk (p x)
  have hv : IsPreimmersion v := inferInstanceAs (IsPreimmersion (S.fromSpecStalk (p x)))
  have hev : etaK V K ≫ v = S.fromSpecStalk (genericPoint S) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec S).specializes trivial)
  have hpt : ∀ z, (etaK V K ≫ v) z = genericPoint S := fun z ↦ by
    rw [hev, Subsingleton.elim z (IsLocalRing.closedPoint K)]
    exact Scheme.fromSpecStalk_closedPoint
  let w : Spec (CommRingCat.of K) ⟶ U := IsOpenImmersion.lift j (etaK V K ≫ v) (by
    rintro _ ⟨z, rfl⟩
    rw [hpt]
    exact hη)
  have hw : w ≫ j = etaK V K ≫ v := IsOpenImmersion.lift_fac _ _ _
  let g := pullback.fst p v
  let pV := pullback.snd p v
  have hg : IsPreimmersion g := MorphismProperty.pullback_fst _ _ hv
  let eV : Spec (CommRingCat.of V) ⟶ pullback p v := pullback.lift (v ≫ e) (𝟙 _) (by simp [he])
  have heV : eV ≫ pV = 𝟙 _ := pullback.lift_snd _ _ _
  have heV' : eV ≫ g = v ≫ e := pullback.lift_fst _ _ _
  let k := pullback.fst pV (etaK V K)
  let pK := pullback.snd pV (etaK V K)
  have hP' : IsPullback (k ≫ g) pK p (etaK V K ≫ v) :=
    (IsPullback.of_hasPullback pV (etaK V K)).paste_horiz (IsPullback.of_hasPullback p v)
  let eK : Spec (CommRingCat.of K) ⟶ pullback pV (etaK V K) :=
    pullback.lift (etaK V K ≫ eV) (𝟙 _) (by simp [heV])
  have heK : eK ≫ k = etaK V K ≫ eV := pullback.lift_fst _ _ _
  have heK' : eK ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  let q : pullback pV (etaK V K) ⟶ HU := hP.lift (k ≫ g) (pK ≫ w)
    (by rw [hP'.w, Category.assoc, hw])
  have hq : q ≫ jH = k ≫ g := hP.lift_fst _ _ _
  have hjH : Mono jH := MorphismProperty.of_isPullback (P := .monomorphisms _) hP.flip
    (inferInstanceAs (Mono j))
  have heq : eK ≫ q = w ≫ eU := by
    rw [← cancel_mono jH, Category.assoc, hq, ← Category.assoc, heK, Category.assoc, heV',
      Category.assoc, heU, ← Category.assoc w, hw, Category.assoc]
  obtain ⟨c, hc'⟩ := exists_gen_germ V K pV eV inferInstance inferInstance heV eK heK hL
    (fun i ↦ g ≫ φ i) ε (fun i ↦ q ≫ jH ≫ φ i)
    (funext fun i ↦ by rw [← Category.assoc, hq, Category.assoc])
    (fun i ↦ v ≫ e ≫ φ i) (funext fun i ↦ by rw [← Category.assoc, ← heV', Category.assoc])
    (LB.pullGen L _ _ t q) (LB.pullGen L _ _ ρ v) (DVR.pullGen_isGen _ _ _ _ ht _)
    (DVR.pullGen_isGen _ _ _ _ hρ _) (corr_of_val hL fun y J hJ ↦ by
      have := val_corr hJ hc w
      rw [val_pull hJ, val_pull hJ] at this
      rw [val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
        heq, ← hw, this])
  have hpη : p (genericPoint H) = genericPoint S := by
    have : Surjective p := ⟨fun s ↦ ⟨e s, by rw [← Scheme.Hom.comp_apply, he]; rfl⟩⟩
    have h := (genericPoint_spec H).image p.continuous
    rw [Set.image_univ, p.surjective.range_eq, closure_univ] at h
    exact h.eq (genericPoint_spec S)
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hP' (genericPoint H)
    (IsLocalRing.closedPoint K) (hpη.trans (hpt _).symm)
  obtain ⟨y, hyx, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback p v) x
    (IsLocalRing.closedPoint V) (Scheme.fromSpecStalk_closedPoint).symm
  have : Nonempty (LB.wchart L φ a) := ⟨⟨_, hxa⟩⟩
  have hzA : (k ≫ g) z ∈ A := hz ▸ genericPoint_mem_opens A
  have hza : (k ≫ g) z ∈ LB.wchart L φ a := hz ▸ genericPoint_mem_opens _
  have hkz : k z ∈ LB.wchart L (fun i ↦ g ≫ φ i) a := (wchart_comp L g φ a).ge hza
  have hqz : q z ∈ LB.wchart L (fun i ↦ jH ≫ φ i) a :=
    (wchart_comp L jH φ a).ge (show (q ≫ jH) z ∈ LB.wchart L φ a from hq ▸ hza)
  have hy : y ∈ LB.wchart L (fun i ↦ g ≫ φ i) a :=
    (wchart_comp L g φ a).ge (show g y ∈ LB.wchart L φ a from
      (congrArg (· ∈ LB.wchart L φ a) hyx).mpr hxa)
  have hm : (𝟙 _ : pullback pV (etaK V K) ⟶ _) z ∈
      LB.wchart L (fun i ↦ q ≫ jH ≫ φ i) a := (wchart_comp L q (fun i ↦ jH ≫ φ i) a).ge hqz
  have hgm : gm k z (LB.wchart L (fun i ↦ g ≫ φ i) a) (c.s a) = gm (k ≫ g) z A τ := by
    rw [← hq, hτ _ q z (show (q ≫ jH) z ∈ A from hq ▸ hzA)]
    exact (hc' z a hkz).trans ((gm_res _ z _ hm _).trans ((gm_pull _ _ z _ hqz _).trans
      (by rw [Category.id_comp]; rfl)))
  rw [← hyx]
  constructor
  · refine mem_range_of_preimmersion g k z hz y A _ _ hy (LB.ts c a).val ?_
    rw [gs_unit _ _ _ hkz, gs_unit _ _ _ hzA]
    exact congrArg Units.val hgm
  · refine mem_range_of_preimmersion g k z hz y A _ _ hy (LB.ts c a)⁻¹.val ?_
    rw [gs_unit _ _ _ hkz, gs_unit _ _ _ hzA, map_inv, map_inv]
    exact congrArg (fun u ↦ Units.val u⁻¹) hgm
end GlobalTheory.GenExtendNormal
