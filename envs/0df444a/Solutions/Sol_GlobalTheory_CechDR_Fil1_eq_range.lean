-- Prove2me | solution 1 for GlobalTheory.CechDR.Fil1_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:02:49.496023+00:00
-- url     : https://prove2.me/submissions/8bb56c95-95d5-45eb-a6ab-982f0d7de94e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_toO_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
variable {F}
variable (F)
namespace GlobalTheory.CechDR
theorem _root_.solution : Fil1 F = LinearMap.range (ofForm F) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := Hyp1.mk_surjective F x
    rw [Fil1, LinearMap.mem_ker, toO_mk, H1.mk_eq_zero] at hx
    obtain ⟨g, hg⟩ := hx
    have hg' : d0 F g = c.1.1 := hg
    let c' : cechDeRhamTotalCocyclesOne F := c - ⟨dTot0 F g, dTot0_mem F g⟩
    have h1 : c'.1.1 = 0 := by
      show c.1.1 - d0 F g = 0
      rw [hg', sub_self]
    have hm := mem_cechDeRhamTotalCocyclesOne_iff.1 c'.2
    let ω : Closed1 F := ⟨⟨c'.1.2, by
      intro T T' φ
      have e := hm.2.1 φ
      rw [h1] at e
      simpa using e⟩, by
      intro T
      exact hm.2.2 T⟩
    refine ⟨ω, ?_⟩
    show Hyp1.mk F (formZZ F ω) = Hyp1.mk F c
    have hω : formZZ F ω = c' := Subtype.ext (Prod.ext h1.symm rfl)
    rw [hω, Hyp1.mk_eq_mk]
    refine ⟨-g, ?_⟩
    rw [map_neg]
    show -dTot0 F g = (c.1 - dTot0 F g) - c.1
    abel
  · rintro ⟨ω, rfl⟩
    rw [Fil1, LinearMap.mem_ker]
    show toO F (Hyp1.mk F (formZZ F ω)) = 0
    rw [toO_mk, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    rfl
end GlobalTheory.CechDR
