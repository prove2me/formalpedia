-- Prove2me | solution 1 for KernelRank.borderTotalCost_le_of_tendsto_radial_real_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:56:43.60122+00:00
-- url     : https://prove2.me/submissions/5c1ce3b6-d148-4c96-8b00-bce772a020e1

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_totalCost_le_of_tendsto_radial_profile
import Theorems.Thm_KernelRank_borderTotalCost_eq_totalCost_of_forall_im_eq_zero

set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d)
    {cs : List Component} (hcs : IsRepresentation cs) (him : ∀ c ∈ cs, c.rate.im = 0)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℝ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (profile cs (∑ j, x j ^ 2)))) :
    borderTotalCost d cs ≤ r := by
  rw [borderTotalCost_eq_totalCost_of_forall_im_eq_zero d him]
  exact totalCost_le_of_tendsto_radial_profile hd hcs hrank htend
end KernelRank
