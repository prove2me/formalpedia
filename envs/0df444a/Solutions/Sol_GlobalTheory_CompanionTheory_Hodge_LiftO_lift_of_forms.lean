-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.lift_of_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:03.402028+00:00
-- url     : https://prove2.me/submissions/de6e14c6-be28-47f2-89bd-160912541608

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_class_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_prim
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_closed_of_conn
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution : OneFormCohSt → TwoFormCohSt → LiftSt := by
  intro h1 h2 R _ C _ F hF hBi hC c
  obtain ⟨E, _, G, m, p, q, hSG, hPG, hH, hW, hm1, hmW, -⟩ := hBi
  have hFG : Framed G := by
    obtain ⟨-, -, hfin, hproj⟩ := hF
    let e : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G :=
      LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q)) hW
    exact ⟨hSG, hPG, Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  obtain ⟨muF, hmF, hmS, -⟩ := h1 R C F hF
  obtain ⟨muG, hmG, -, hG3⟩ := h1 R E G hFG
  obtain ⟨νF, hνF, -, hsurj⟩ := h2 R C F hF
  obtain ⟨νG, hνG, hinj, -⟩ := h2 R E G hFG
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  obtain ⟨t, ht⟩ := hmS (fun T T' φ ↦ KaehlerDifferential.D R _ (f.1 T T' φ)) (fun T T' T'' φ ψ ↦ by
    rw [Z1.comp f, map_add, p1_D])
  have hz := class_zero m p q hH hW hm1 hmW muF muG hmF hmG hG3 f t (fun T T' φ ↦ congrFun (congrFun (congrFun ht T) T') φ)
  obtain ⟨β, hβ⟩ := exists_prim muF hmF t hz
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ) :=
    fun T T' φ ↦ by
      have e : KaehlerDifferential.D R _ (f.1 T T' φ) = β T' - p1 F φ (β T) :=
        (congrFun (congrFun (congrFun ht T) T') φ).symm.trans (hβ T T' φ)
      rw [e]; abel
  haveI := hF.2.2.1
  haveI := hF.2.2.2
  have hcl := closed_of_conn m p q hW hm1 hmW hC νF νG hνF hνG hinj hsurj f β hconn
  exact ⟨Hyp1.mk F ⟨(f.1, β), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hcl⟩⟩, rfl⟩
end GlobalTheory.CompanionTheory.Hodge.LiftO
