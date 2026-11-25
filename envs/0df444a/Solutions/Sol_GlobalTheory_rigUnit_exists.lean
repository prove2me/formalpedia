-- Prove2me | solution 1 for GlobalTheory.rigUnit_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:54:05.022175+00:00
-- url     : https://prove2.me/submissions/e3c51dfa-2ec7-4f40-a32d-003461b767cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBaseUnitRigidifiedGenericGenerator
import Theorems.Thm_GlobalTheory_rigUnit_exists_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_genPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  intro R K _ _ _ _ _ X e he eA heA M rig c hM hrig hcorr a u hu H
  obtain ⟨w, hw⟩ := rigUnit_exists_ratio M hM e (LB.genPull M u e) rig (LB.isGen_genPull M u hu e) hrig
  haveI : Epi (CommRingCat.ofHom (algebraMap R K)) := by
    have := IsLocalization.epi (nonZeroDivisors R) K
    exact this
  haveI : Mono (spMap (algebraMap R K)) := by
    exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))
  have hsnd : eA ≫ pullback.snd X.hom (spMap (algebraMap R K)) = 𝟙 _ := by
    rw [← cancel_mono (spMap (algebraMap R K)), Category.assoc, ← pullback.condition, ← Category.assoc, heA,
      Category.assoc, he, Category.comp_id, Category.id_comp]
  let z : Sp K := (⊥ : PrimeSpectrum K)
  choose J hJ using fun χ : Sp K ⟶ X.left => exists_chart hM (χ z)
  have hG : Good M z J := hJ
  have hv := val_corr hG hcorr (𝟙 _)
  rw [val_pull hG, val_pull hG, Category.id_comp, Category.id_comp,
    val_of (L := M) c eA z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => by rw [heA]),
    val_of (L := M) rig _ z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => rfl)] at hv
  have hi := hJ (spMap (algebraMap R K) ≫ e)
  generalize J (spMap (algebraMap R K) ≫ e) = i at hv hi
  have h1 := H i _ eA z (by
    have : (eA ≫ pullback.fst X.hom (spMap (algebraMap R K))) z ∈ M.U i := by rw [heA]; exact hi
    exact this)
  rw [heA, hsnd] at h1
  have hm : spMap (algebraMap R K) z ∈ (M.pull e).U (fun _ => i) := mem_pull.2 hi
  have h2 := hw _ (spMap (algebraMap R K)) z (fun _ => i) hm
  have h3 : gm (spMap (algebraMap R K)) z ((M.pull e).U (fun _ => i)) ((LB.genPull M u e).s (fun _ => i)) =
      gm (spMap (algebraMap R K) ≫ e) z (M.U i) (u.s i) :=
    (gm_res _ z _ hm _).trans (gm_pull _ e z _ hi _)
  have h4 : (gm (spMap (algebraMap R K)) z ⊤ w).val =
      gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
    have h5 := (congrArg Units.val (h2.symm.trans h3)).trans (h1.trans (congrArg (_ * ·) (congrArg Units.val hv)))
    rw [Units.val_mul] at h5
    exact (Units.mul_left_inj _).1 h5
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, ?_⟩
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  apply φ.injective
  rw [gm_val _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at h4
  refine Eq.trans ?_ h4
  change ((Sp K).presheaf.germ ⊤ z trivial).hom _ = ((Sp K).presheaf.germ ⊤ z trivial).hom _
  congr 1
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Iso.hom_inv_id_apply] at n
  exact n
end GlobalTheory
