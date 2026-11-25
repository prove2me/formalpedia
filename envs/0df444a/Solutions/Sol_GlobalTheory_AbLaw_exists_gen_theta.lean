-- Prove2me | solution 1 for GlobalTheory.AbLaw.exists_gen_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:35:46.956453+00:00
-- url     : https://prove2.me/submissions/f3922a9e-da46-4449-a709-2db10dc03ef1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_TrivAt_comp
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_trivAt_of_formal
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_triv_of_local
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_triv_pull_comp_iff
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_isOpen_locTriv
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_locTriv_subset
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_fibTriv_clopen
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_exists_cube_chart
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_prod_face
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_one_left_fst
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_isAb_baseChange
import Theorems.Thm_GlobalTheory_AbLaw_isLB_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd


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
open GlobalTheory GlobalTheory.AbLaw
open CubeGen
namespace GlobalTheory.AbLaw
theorem _root_.solution :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → GlobalFnsSt → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (R : Type) [CommRing R] (X Y : Over (Spec (CommRingCat.of R))), IsProjBy X.hom → IsProjBy Y.hom → IsProjBy (X ⊗ Y).hom) → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → IsClosed {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)}) → (∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → Nonempty (Perf (A ⊗ A).hom M) → Triv (M.pull (lift (𝟙 A) 1).left) → Triv (M.pull (lift 1 (𝟙 A)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (A ⊗ A).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (A ⊗ A).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((A ⊗ A).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι)) → ∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen := by
  intro hI hG hPerf hProj hSegre hClosed hOpen S P M hM
  have hA := P.isAb
  have := hA.comm
  have := hA.geomConnected
  have H := fibTriv_clopen M (thφ P.A (x3 P.A)) thε (x3 P.A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart P.A j
    have hB := isAb_baseChange hA (j ≫ P.A.hom)
    have one := one_left_fst (A := P.A) (j ≫ P.A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ P.A.hom)).obj P.A).hom := by
      obtain ⟨N, -, m, s, h₁, h₂⟩ := hProj S P R (j ≫ P.A.hom) _ _ _ (IsPullback.of_hasPullback _ _)
      exact ⟨_, h₁, m, s, h₂⟩
    let B := (Over.pullback (j ≫ P.A.hom)).obj P.A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ thφ P.A (x3 P.A) k) thε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := hPerf R _ _ sm (hSegre R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, hClosed R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr (hI _ _ _ sm gc),
      fun F _ g Z π f' => hOpen R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 1 (B.hom ≫ j ≫ P.A.hom) ?_)
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 0 (B.hom ≫ j ≫ P.A.hom) ?_)
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M (thφ P.A (x3 P.A)) thε (x3 P.A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M (thφ P.A (x3 P.A)) thε (x3 P.A 2).left := fun t => by
    have hr : Set.range (S.fromSpecResidueField (P.A.hom t)) = {P.A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := S.fromSpecResidueField (P.A.hom t) ≫ η[P.A].left
    have gw : g ≫ P.A.hom = S.fromSpecResidueField (P.A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (P.A.hom.isConnected_preimage_singleton (P.A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec (S.residueField (P.A.hom t)) ⟶ S => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨S.residueField (P.A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 P.A 2).left g,
      trivAt_of_formal hM _ (prod_face _ 2 (pullback.snd _ g ≫ S.fromSpecResidueField (P.A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm))⟩
  let e : P.A ⟶ G3 P.A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 P.A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 P.A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM (thφ P.A (x3 P.A)) thε (x3 P.A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => prod_face _ 0 (b ≫ P.A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart P.A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ P.A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2
end GlobalTheory.AbLaw
