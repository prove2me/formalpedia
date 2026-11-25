-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.triv_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:38:23.986206+00:00
-- url     : https://prove2.me/submissions/53518c3b-aed2-4bd8-98e1-f46c0cd47737

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y Z Z' T : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ T) (e : T ⟶ Y)
    (he : e ≫ p = 𝟙 T)
    (hF : ∀ (Z : Scheme.{0}) (b : Z ⟶ T) (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
      ∏ i, k ((b ≫ e) ≫ φ i) ^ ε i = 1)
    (hs : ∀ V : T.Opens, ∃ (Z : Scheme.{0}) (m : Z ⟶ Y) (q : Z ⟶ V.toScheme), IsPullback m q p V.ι ∧
      Function.Surjective q.appTop.hom)
    (h : ∀ s : T, ∃ U : T.Opens, s ∈ U ∧ TrivAt L φ ε (p ⁻¹ᵁ U).ι) : Triv (LB.LinComb L φ ε) := by
  have loc : ∀ s : T, ∃ U : T.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ φ i) ε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (b : Z ⟶ T) (z : Z) (J), Good L z J →
        r ≫ (p ⁻¹ᵁ U).ι = b ≫ e → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
        n ≫ (p ⁻¹ᵁ U).ι = ((p ⁻¹ᵁ U).ι ≫ p) ≫ e :=
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι (((p ⁻¹ᵁ U).ι ≫ p) ≫ e) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q (p y.1)) he
        exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => (p ⁻¹ᵁ U).ι ≫ φ i) (ε' := ε)
      (fun V _ k => by
        have p' := hF _ ((p ⁻¹ᵁ U).ι ≫ p) V k
        rw [← n₁] at p'
        simp only [Category.assoc] at p'
        refine (Fintype.prod_sum_type _).trans ?_
        simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, p', inv_one, _root_.mul_one])
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono (p ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, ← Category.assoc, hr,
        Category.assoc b, he, Category.comp_id]
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc
  have agree : ∀ (s s' : T) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ (p ⁻¹ᵁ U s).ι = r' ≫ (p ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    obtain ⟨W, pr, q, hq, sq⟩ := hs (U s ⊓ U s')
    have mk : ∀ V : T.Opens, U s ⊓ U s' ≤ V → ∃ m : W ⟶ (p ⁻¹ᵁ V).toScheme, m ≫ (p ⁻¹ᵁ V).ι = pr := fun V hV =>
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ V).ι pr (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q y) hq.w
        exact (congrArg (· ∈ V) e').mpr (hV (q y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e₀ : (U s ⊓ U s').toScheme ⟶ W := hq.lift ((U s ⊓ U s').ι ≫ e) (𝟙 _)
      (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
    have he₀ : e₀ ≫ pr = (U s ⊓ U s').ι ≫ e := hq.lift_fst _ _ _
    let v : Z ⟶ (U s ⊓ U s').toScheme := IsOpenImmersion.lift (U s ⊓ U s').ι ((r ≫ (p ⁻¹ᵁ U s).ι) ≫ p) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩)
    let ρ : Z ⟶ W := hq.lift (r ≫ (p ⁻¹ᵁ U s).ι) v (IsOpenImmersion.lift_fac _ _ _).symm
    have hρ : ρ ≫ pr = r ≫ (p ⁻¹ᵁ U s).ι := hq.lift_fst _ _ _
    have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
    have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
    have key := gen_unique' hL (φ := fun i => m ≫ (p ⁻¹ᵁ U s).ι ≫ φ i) (ε := ε)
      (φ' := fun i => m' ≫ (p ⁻¹ᵁ U s').ι ≫ φ i) (ε' := ε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      q e₀ (hq.lift_snd _ _ _) sq (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        rw [val_pull hI, val_pull hI, hn s _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm, he₀]),
          hn s' _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm', he₀])]) Z ρ z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, -⟩ := glue_gen hL φ ε (fun s => p ⁻¹ᵁ U s) (fun y => ⟨p y, hU _⟩) t ht agree
  exact ⟨u, hu⟩
end GlobalTheory.AbLaw.CubeGen
