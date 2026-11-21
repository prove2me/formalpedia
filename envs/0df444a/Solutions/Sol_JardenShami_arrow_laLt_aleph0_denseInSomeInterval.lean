-- Prove2me | solution 1 for JardenShami.arrow_laLt_aleph0_denseInSomeInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:01.052056+00:00
-- url     : https://prove2.me/submissions/3daab214-024f-47ae-8b9e-4a853b533844

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Theorems.Thm_JardenShami_arrow_laLt_aleph0_of_arrow_addLt_aleph0

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
namespace JardenShami
theorem _root_.solution (I : Type w) [LinearOrder I] [DenselyOrdered I]
    (hfact : Fact_3_4.{v, w} I) :
    Arrow (denseInSomeInterval I) (denseInSomeInterval I) (laLt (ℵ₀ : Cardinal.{v})) := by
  exact arrow_laLt_aleph0_of_arrow_addLt_aleph0 _ hfact
end JardenShami
