-- Prove2me | solution 1 for GlobalTheory.kTriv_of_sections_vanish_on_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:21.530444+00:00
-- url     : https://prove2.me/submissions/7d762ec7-0ecc-4dd3-8d89-06f24001a73e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsGenTranslDiffComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_KernelPolarisationTrivialOfSectionsVanishZero
import Theorems.Thm_GlobalTheory_appLE_top_eq_zero_iff_gs
import Theorems.Thm_GlobalTheory_exists_sec_of_gen_diff
import Theorems.Thm_GlobalTheory_exists_isGen_translDiff_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → (∀ (R' : Type) [CommRing R'] (f : Sp R' ⟶ S) (Y : Scheme.{0}) (φ : Y ⟶ A.left) (q : Y ⟶ Sp R'), IsPullback φ q A.hom f → ∀ (s : (L.pull φ).Sec) (T : Scheme.{0}) (t : T ⟶ Y) (j : (L.pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ (L.pull φ).U j), t ≫ φ = t ≫ φ ≫ A.hom ≫ eSec A → (t.appLE ((L.pull φ).U j) ⊤ h).hom (s.f j) = 0) → Out.KTriv A L := by
  intro S A _ L θ hL hθ hs R _ t x hx
  have one : ∀ (T : Over S) (y : T ⟶ A), y.left ≫ A.hom ≫ eSec A = (1 : T ⟶ A).left := fun T y => by
    rw [← Category.assoc, Over.w y]; rfl
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ S) (y : Over.mk t' ⟶ A) (i i₀ : L.ι),
      ⊤ ≤ y.left ⁻¹ᵁ L.U i → ⊤ ≤ (1 : Over.mk t' ⟶ A).left ⁻¹ᵁ L.U i₀ →
      (∃ c : LB.Gen (Out.translDiff A L y), c.IsGen) → y = 1 := by
    rintro R' t' y i i₀ hi hi₀ ⟨c, hc⟩
    by_contra hne
    have hne' : y.left ≠ (1 : Over.mk t' ⟶ A).left := fun e => hne (Over.OverMorphism.ext e)
    obtain ⟨s, hs'⟩ := exists_sec_of_gen_diff hL θ _ _ c hc
    let r : Over.mk t' ⟶ Over.mk t' ⊗ A := lift (𝟙 _) 1
    have r₁ : r.left ≫ (lift (fst _ A ≫ y) (snd _ A) ≫ μ[A]).left = y.left := by
      rw [← Over.comp_left, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]
      exact congrArg (fun q : Over.mk t' ⟶ A => q.left) (_root_.mul_one y)
    have r₂ : r.left ≫ (snd _ A).left = (1 : Over.mk t' ⟶ A).left := by
      rw [← Over.comp_left, lift_snd]
    have hj : ⊤ ≤ r.left ⁻¹ᵁ (L.pull (snd (Over.mk t') A).left).U (fun _ => i₀) := fun z _ =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q z ∈ L.U i₀) r₂).mpr (hi₀ trivial)
    have hz := hs R' t' _ (snd (Over.mk t') A).left (fst (Over.mk t') A).left
      (IsPullback.of_hasPullback t' A.hom).flip s _ r.left (fun _ => i₀) hj
      (by rw [← Category.assoc, r₂, one])
    refine hne' (((hθ _ y.left i hi).1 ((appLE_top_eq_zero_iff_gs _ _ hi _).2 fun z => ?_)).trans (one _ y))
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Bool)
      (fun b => cond b y.left (1 : Over.mk t' ⟶ A).left) (fun b => cond b i i₀) (by
        rintro (_ | _) (_ | _) e
        exacts [rfl, absurd e.symm hne', absurd e hne', rfl]) (by
        rintro (_ | _)
        exacts [hi₀ trivial, hi trivial])
    have := hs' _ r.left z J hJ ((sval_of s r.left z J (fun _ => i₀) (fun _ => by rw [r₂]; exact e false)).trans
      ((appLE_top_eq_zero_iff_gs _ _ hj _).1 hz z))
    rw [r₁] at this
    obtain rfl : J y.left = i := e true
    exact this
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((1 : Over.mk t ⟶ A).left p)
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (U := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ A).left ⁻¹ᵁ L.U i₀) (x := p) ⟨⟨hp, hi⟩, hi₀⟩
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have hq := fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    refine H' _ _ _ i i₀ (fun q _ => (hq q).1.2) ?_ (exists_isGen_translDiff_comp A L x g V
      (fun q => (hq q).1.1) c hc)
    rw [← MonObj.comp_one g]
    exact fun q _ => (hq q).2
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2
end GlobalTheory
