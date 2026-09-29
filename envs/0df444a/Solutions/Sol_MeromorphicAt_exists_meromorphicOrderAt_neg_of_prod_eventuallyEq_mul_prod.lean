-- Prove2me | solution 1 for MeromorphicAt.exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f03a9660-7bef-503a-a049-1ff54904ca39

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod

set_option autoImplicit false

open Filter Topology

namespace R5

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}

theorem exists_neg_of_prod_neg
    {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hprod : meromorphicOrderAt (∏ i ∈ s, f i) x < 0) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  by_contra h
  push Not at h
  have hsum : (0 : WithTop ℤ) ≤ ∑ i ∈ s, meromorphicOrderAt (f i) x :=
    Finset.sum_nonneg h
  rw [meromorphicOrderAt_prod hf] at hprod
  exact absurd (lt_of_le_of_lt hsum hprod) (lt_irrefl _)

theorem exists_neg_of_prod_eventuallyEq
    {s : Finset ι} {f : ι → 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hfg : ∀ᶠ z in 𝓝[≠] x, (∏ i ∈ s, f i z) = g z)
    (hg : meromorphicOrderAt g x < 0) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  refine exists_neg_of_prod_neg hf ?_
  have : (∏ i ∈ s, f i) =ᶠ[𝓝[≠] x] g := by
    filter_upwards [hfg] with z hz
    simpa [Finset.prod_apply] using hz
  rwa [meromorphicOrderAt_congr this]

end R5

open Filter Topology in

theorem R5.single
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}
    {s : Finset ι} {f : ι → 𝕜 → 𝕜} {p h : 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hp : MeromorphicAt p x) (hpole : meromorphicOrderAt p x < 0)
    (hh : AnalyticAt 𝕜 h x) (hh0 : h x ≠ 0)
    (hfg : ∀ᶠ z in nhdsWithin x {x}ᶜ, (∏ i ∈ s, f i z) = p z * h z) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  refine R5.exists_neg_of_prod_eventuallyEq hf hfg ?_
  have hh' : meromorphicOrderAt h x = 0 := by
    rw [hh.meromorphicOrderAt_eq, hh.analyticOrderAt_eq_zero.mpr hh0]
    rfl
  have hmul : meromorphicOrderAt (p * h) x = meromorphicOrderAt p x + meromorphicOrderAt h x :=
    meromorphicOrderAt_mul hp hh.meromorphicAt
  show meromorphicOrderAt (fun z => p z * h z) x < 0
  have : (fun z => p z * h z) = p * h := rfl
  rw [this, hmul, hh', add_zero]
  exact hpole

open Filter Topology in
theorem solution
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι κ : Type*}
    {s : Finset ι} {t : Finset κ} {f : ι → 𝕜 → 𝕜} {p : 𝕜 → 𝕜} {h : κ → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hp : MeromorphicAt p x) (hpole : meromorphicOrderAt p x < 0)
    (hh : ∀ j ∈ t, AnalyticAt 𝕜 (h j) x) (hh0 : ∀ j ∈ t, h j x ≠ 0)
    (hfg : ∀ᶠ z in nhdsWithin x {x}ᶜ, (∏ i ∈ s, f i z) = p z * ∏ j ∈ t, h j z) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  refine R5.single (h := fun z => ∏ j ∈ t, h j z) hf hp hpole
    (Finset.analyticAt_fun_prod t hh) ?_ hfg
  exact Finset.prod_ne_zero_iff.mpr hh0

end S_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
end P2MW
export P2MW.S_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod (solution)
