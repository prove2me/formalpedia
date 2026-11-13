-- Prove2me | solution 1 for HDXHitting.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:53.57352+00:00
-- url     : https://prove2.me/submissions/7590515c-2958-40b8-9ef3-7bc2c545652a

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly
import Theorems.Thm_HDXHitting_lemma_3_2_one_sided
import Theorems.Thm_HDXHitting_eq_3

section
set_option autoImplicit false
namespace HDXHitting

theorem chk_lemma_3_2 {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d : ℕ)
    (hd : 1 ≤ d) (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (c : V → ι) (S : Finset ι) :
    (IsOneSidedHDX d p lam → hit p f ≤ mean d p f * (mean d p f + d * lam) ^ (d - 1)) ∧
      (S.card = d → IsRainbow p c S → IsPartiteHDX p c S lam →
        hit p f ≤ cPoly S lam (colourMean p c f)) :=
  ⟨fun hX => lemma_3_2_one_sided d hd p hp lam hlam hX f hf,
   fun hS hc hX => eq_3 d hd p hp c S hS hc lam hlam hX f hf⟩

end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_lemma_3_2 := @HDXHitting.chk_lemma_3_2
