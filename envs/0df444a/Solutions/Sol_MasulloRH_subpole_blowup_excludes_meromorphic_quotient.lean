-- Prove2me | solution 1 for MasulloRH.subpole_blowup_excludes_meromorphic_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:47:21.150122+00:00
-- url     : https://prove2.me/submissions/cd643d5d-df95-4ecd-b1eb-80df98252e90

import Mathlib
open Filter Topology
theorem solution (f : ℂ → ℂ) (a : ℂ) (l : Filter ℂ) [l.NeBot]
    (hl : l ≤ 𝓝[≠] a)
    (hinf : Tendsto (fun z => ‖f z‖) l atTop)
    (hsub : Tendsto (fun z => ‖(z-a)*f z‖) l (𝓝 0)) :
    ¬ MeromorphicAt f a := by
  intro hf
  have negord : meromorphicOrderAt f a < 0 := by
    by_contra! hn
    obtain ⟨c,hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf hn
    exact not_tendsto_atTop_of_tendsto_nhds (hc.norm.mono_left hl) hinf
  let q : ℂ → ℂ := fun z => (z-a)*f z
  have hs : MeromorphicAt (fun z : ℂ => z-a) a := by fun_prop
  have hq : MeromorphicAt q a := hs.mul hf
  have hqo : meromorphicOrderAt q a ≤ 0 := by
    change meromorphicOrderAt ((fun z : ℂ => z-a)*f) a ≤ 0
    rw [meromorphicOrderAt_mul hs hf,meromorphicOrderAt_id_sub_const]
    obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp negord.ne_top
    rw [← hm] at negord ⊢
    have hmneg : m < 0 := by exact_mod_cast negord
    exact_mod_cast (show 1+m ≤ 0 by omega)
  rcases hqo.lt_or_eq with hlt|heq
  · have h := tendsto_cobounded_of_meromorphicOrderAt_neg hlt
    have ht := (tendsto_norm_atTop_iff_cobounded.mpr h).mono_left hl
    exact not_tendsto_atTop_of_tendsto_nhds hsub ht
  · obtain ⟨c,hc,ht⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hq heq
    have hcz : ‖c‖ = 0 := tendsto_nhds_unique (ht.norm.mono_left hl) hsub
    exact hc (norm_eq_zero.mp hcz)
