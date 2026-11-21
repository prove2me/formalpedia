-- Prove2me | solution 1 for JardenShami.isStarLocallyAdditive_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:15.993297+00:00
-- url     : https://prove2.me/submissions/1c442b13-9f49-43f1-866e-843c7bb24c7c

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_Coloring_color_dual
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) :
    IsStarLocallyAdditive C ↔
      ∀ (x y z w : A) (hxy : x < y) (hyz : y < z) (hzw : z < w),
        C.color y z hyz = C.color x z (hxy.trans hyz) →
          C.color y w (hyz.trans hzw) = C.color x w ((hxy.trans hyz).trans hzw) := by
  constructor
  · intro hC x y z w hxy hyz hzw h
    have := hC (OrderDual.toDual w) (OrderDual.toDual z) (OrderDual.toDual y)
      (OrderDual.toDual x) hzw hyz hxy
    have e := this ((Coloring.color_dual C (OrderDual.toDual z) (OrderDual.toDual y) hyz).trans
      (h.trans (Coloring.color_dual C (OrderDual.toDual z) (OrderDual.toDual x)
        (hxy.trans hyz)).symm))
    exact (Coloring.color_dual C (OrderDual.toDual w) (OrderDual.toDual y)
      (hyz.trans hzw)).symm.trans (e.trans (Coloring.color_dual C (OrderDual.toDual w)
        (OrderDual.toDual x) ((hxy.trans hyz).trans hzw)))
  · intro hC a b c d hab hbc hcd h
    simp only [Coloring.color_dual] at h ⊢
    exact hC (OrderDual.ofDual d) (OrderDual.ofDual c) (OrderDual.ofDual b) (OrderDual.ofDual a)
      hcd hbc hab h
end JardenShami
