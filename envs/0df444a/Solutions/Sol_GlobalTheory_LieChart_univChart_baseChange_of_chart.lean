-- Prove2me | solution 1 for GlobalTheory.LieChart.univChart_baseChange_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:52.766447+00:00
-- url     : https://prove2.me/submissions/ee612472-aa3e-4399-adc3-51a81b0baed8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_aug_surj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapA_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_elt_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isUnivRing_bc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetMapA_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_le_preimage_of_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_nil_of_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_eps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_pullR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_jetAug_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
namespace GlobalTheory.LieChart
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (C : Chart G) (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G)
    (hx : IsUnivChart G n x) :
    ∃ x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (fB R R')).obj G,
      IsUnivChart _ n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (algebraMap R R' ∘ c)).left ≫ pullback.fst G.hom (fB R R') =
          Spec.map (CommRingCat.ofHom (dualMapR (algebraMap R R'))) ≫ (tvec (x := x) c).left := by
  have hin : ∀ m, ∃ π : Γ(G.left, C.U) →ₐ[R] JetR R (Fin n) m, x m = pt C π := fun m =>
    exists_pt C (x m) (le_preimage_of_nil C (jetAug R (Fin n) m) (aug_surj _)
      (elt_nil _ (ker_jetAug_nil (Fin n) m)) (x m) ((Algebra.ofId R R).comp (eps C))
      ((spMap_jetAug_alt hx m).trans (pt_eps C R).symm))
  choose π hπ using hin
  have hoe : (Algebra.ofId R R).comp (eps C) = eps C := AlgHom.ext fun _ => rfl
  have hπa : ∀ m, (jetAug R (Fin n) m).comp (π m) = eps C := fun m => by
    rw [← hoe]
    apply pt_injective C
    rw [← spMap_pt, ← hπ, spMap_jetAug_alt hx, pt_eps]
  have hπtr : ∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m := fun m =>
    pt_injective C (by rw [← spMap_pt, ← hπ, ← hπ, hx.1 m])
  have hπ0 : ∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp (eps C) := fun m =>
    pt_injective C (by rw [← spMap_pt, ← hπ, hx.2.1 m, pt_eps])
  have huniv : ∀ m, IsUnivRing (eps C) m (π m) := by
    intro m A _ _ aug hJ h hh
    have hy : spMap aug ≫ pt C h = 1 := by rw [spMap_pt, hh, ← hoe, pt_eps]
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := hx.2.2 A aug m hJ (pt C h) hy
    refine ⟨ψ, ⟨h1, pt_injective C (by rw [← spMap_pt, ← hπ]; exact h2)⟩, fun ψ₂ hψ₂ => hu ψ₂ ⟨hψ₂.1, ?_⟩⟩
    rw [hπ, spMap_pt, ← hψ₂.2]
  refine ⟨fun m => pullR G (pt C ((jetMapA n m).comp (π m))), ⟨fun m => ?_, fun m => ?_, ?_⟩, fun c => ?_⟩
  · apply pushR_inj G
    rw [pushR_spMap, pushR_pullR, pushR_pullR, spMap_pt, ← hπtr m, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    congr 2
    apply jet_ext
    intro j
    show jetTruncR R' (Fin n) m (jetMapA n (m + 1) (zR (m + 1) j)) = jetMapA n m (zR m j)
    rw [jetMapA_zR, jetMapA_zR]
    rfl
  · apply pushR_inj G
    rw [pushR_spMap, pushR_pullR, spMap_pt, pushR_one, ← pt_eps C (JetR R' (Fin n) 0)]
    congr 1
    have e : ((jetZeroR R' (Fin n) m).restrictScalars R).comp (jetMapA n m) = (jetMapA n 0).comp (jetZeroR R (Fin n) m) := by
      apply jet_ext
      intro j
      show jetZeroR R' (Fin n) m (jetMapA n m (zR m j)) = jetMapA n 0 (zR 0 j)
      rw [jetMapA_zR, jetMapA_zR]
      rfl
    rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc, hπ0, ← AlgHom.comp_assoc]
    congr 1
    exact AlgHom.ext fun r => (jetMapA n 0).commutes r
  · intro A _ _ aug m hJ y hy
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hz : spMap (aug.restrictScalars R) ≫ pushR G y = pt C ((Algebra.ofId R R').comp (eps C)) := by
      rw [← pushR_spMap, hy, pushR_one, pt_eps]
    obtain ⟨h, hh⟩ := exists_pt C (pushR G y) (le_preimage_of_nil C (aug.restrictScalars R) (aug_surj aug)
      (fun a ha => elt_nil _ (nil_of_pow _ hJ) a ha) _ _ hz)
    have hha : (aug.restrictScalars R).comp h = (Algebra.ofId R R').comp (eps C) :=
      pt_injective C (by rw [← spMap_pt, ← hh, hz])
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := isUnivRing_bc (eps C) m (π m) (huniv m) (hπa m) A aug hJ h hha
    have key : ∀ ψ' : JetR R' (Fin n) m →ₐ[R'] A,
        y = spMap ψ' ≫ pullR G (pt C ((jetMapA n m).comp (π m))) ↔
          h = (ψ'.restrictScalars R).comp ((jetMapA n m).comp (π m)) := by
      intro ψ'
      constructor
      · intro e
        apply pt_injective C
        rw [← hh, e, pushR_spMap, pushR_pullR, spMap_pt]
      · intro e
        apply pushR_inj G
        rw [hh, e, pushR_spMap, pushR_pullR, spMap_pt]
    exact ⟨ψ, ⟨h1, (key ψ).mpr h2⟩, fun ψ₂ hψ₂ => hu ψ₂ ⟨hψ₂.1, (key ψ₂).mp hψ₂.2⟩⟩
  · have e1 : pushR G (tvec (x := fun m => pullR G (pt C ((jetMapA n m).comp (π m)))) (algebraMap R R' ∘ c)) =
        pt C (((dualLift (algebraMap R R' ∘ c)).restrictScalars R).comp ((jetMapA n 1).comp (π 1))) := by
      show pushR G (spMap _ ≫ _) = _
      rw [pushR_spMap, pushR_pullR, spMap_pt]
    have e2 : spMap (dualMapA R R') ≫ tvec (x := x) c = pt C ((dualMapA R R').comp ((dualLift c).comp (π 1))) := by
      show spMap _ ≫ spMap _ ≫ x 1 = _
      rw [hπ 1, spMap_pt, spMap_pt]
    have e3 : (dualMapA R R').comp ((dualLift c).comp (π 1)) =
        ((dualLift (algebraMap R R' ∘ c)).restrictScalars R).comp ((jetMapA n 1).comp (π 1)) := by
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      congr 1
      apply jet_ext
      intro j
      show dualMapA R R' (dualLift c (zR 1 j)) = dualLift (algebraMap R R' ∘ c) (jetMapA n 1 (zR 1 j))
      rw [jetMapA_zR, dualLift_zR, dualLift_zR, dualMapA_inr]
      rfl
    rw [← pushR_left, e1, ← e3, ← e2]
    rfl
end GlobalTheory.LieChart
