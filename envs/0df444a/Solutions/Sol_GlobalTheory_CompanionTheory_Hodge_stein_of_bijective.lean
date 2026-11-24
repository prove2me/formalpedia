-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.stein_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:33.448283+00:00
-- url     : https://prove2.me/submissions/fa8e2de9-8f7e-417b-bbb0-2228d30ad7ae

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SteinOfBijective
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_eq_of_res_affine
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_exists_global
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_algebraMap_sec

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Hodge
theorem _root_.solution (s : X ⟶ Sp R) (h : Function.Bijective s.appTop.hom) : Stein (OAff s) := by
  have key : ∀ (r : R) (U : X.affineOpens),
      (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) (op U) = X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r U
    exact algebraMap_sec s U.1 r
  refine ⟨?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hg : ∀ (U V : X.affineOpens) (hUV : V.1 ≤ U.1),
          X.presheaf.map (homOfLE hUV).op (y (op U)) = y (op V) := by
        intro U V hUV
        have e := congrFun (congrFun (congrFun hy (op U)) (op V)) (homOfLE (show V ≤ U from hUV)).op
        have e' : (show Γ(X, V.1) from y (op V)) - X.presheaf.map (homOfLE hUV).op (y (op U)) = 0 := e
        exact (sub_eq_zero.mp e').symm
      obtain ⟨t, ht⟩ := exists_global (fun U => y (op U)) hg
      obtain ⟨x, hx⟩ := h.2 t
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x, ?_⟩
      funext T
      have hxinv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
        congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
      have e1 := key ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) T.unop
      rw [hxinv, hx] at e1
      exact e1.trans (ht T.unop)
    · rintro ⟨r, rfl⟩
      funext T T' φ
      have hc : (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) =
          (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' := (GlobalTheory.CatCoh.mp (OAff s) φ).commutes r
      show (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' -
          (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) = 0
      rw [hc, sub_self]
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have e : s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
      apply eq_of_res_affine
      intro V hV
      rw [map_zero]
      have e2 := congrFun hr (op V)
      rw [key] at e2
      exact e2
    have e3 := h.1 (e.trans (map_zero _).symm)
    have hr2 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r :=
      congrArg (fun f => CommRingCat.Hom.hom f r) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
    rw [e3, map_zero] at hr2
    exact hr2.symm
end GlobalTheory.CompanionTheory.Hodge
