-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.altSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:44:40.761099+00:00
-- url     : https://prove2.me/submissions/8be84518-9c0c-4ca7-a80b-9e4e79b05550

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_prim_cup
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_closed_of_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_surj_of_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_one_cob
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_two_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution : OneFormCohSt → TwoFormCohSt → AltSt := by
  intro hOne hTwo R _ C _ F hFr hBi hCl hSurj hcup c
  obtain ⟨D, _, G, m, p, q, hSt, hPar, hb1, hb2, hm1, hm2, hm3⟩ := hBi
  let eG : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G :=
    LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q)) hb2
  haveI := hFr.2.2.1
  haveI := hFr.2.2.2
  have hFrG : Framed G := ⟨hSt, hPar, Module.Finite.equiv eG, Module.Projective.of_equiv eG⟩
  have hcG := closed_of_sum p q hb2.2 hCl
  have hsG := surj_of_sum p q hb1.2 hSurj
  obtain ⟨muF, hF, hsur, -⟩ := hOne R C F hFr
  obtain ⟨muG, hG, -, hker⟩ := hOne R D G hFrG
  obtain ⟨nuF, hνF, -, hνsur⟩ := hTwo R C F hFr
  obtain ⟨nuG, hνG, hνinj, -⟩ := hTwo R D G hFrG
  obtain ⟨z, hz, hzc⟩ := exists_rep hcup c
  have hprim := prim_cup m p q hm3 c
  rw [← hzc] at hprim ⊢
  obtain ⟨β, hβ⟩ := one_cob m p q muF muG hF hG hsur hker hsG hb1 hb2 hm1 hm2 z hz hprim
  let y : cechDeRhamTotalCocyclesTwo F := ⟨dTot1 F (0, β), dTot1_mem F _⟩
  have hy : Hyp2.mk F y = 0 := Hyp2.mk_eq_zero.2 ⟨_, rfl⟩
  have hzy : Hyp2.mk F (z - y) = Hyp2.mk F z := by rw [map_sub, hy, sub_zero]
  have h1 : (z - y).1.1 = 0 := by
    funext T T' T'' φ ψ
    change z.1.1 T T' T'' φ ψ - d1 F 0 T T' T'' φ ψ = 0
    rw [hz, map_zero]
    exact sub_self _
  have h2 : (z - y).1.2.1 = 0 := by
    funext T T' φ
    change z.1.2.1 T T' φ - (β T' - p1 F φ (β T) - KaehlerDifferential.D R _ ((0 : C1 F) T T' φ)) = 0
    rw [hβ]
    simp
  have h3 := two_zero m p q nuF nuG hνF hνG hνinj hνsur hcG hsG hb2 hm2 (z - y) h1 h2
    (by rw [hzy]; exact hprim)
  have h4 : z - y = 0 := Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))
  rw [← hzy, h4, map_zero]
end GlobalTheory.CompanionTheory.HodgeAlt
