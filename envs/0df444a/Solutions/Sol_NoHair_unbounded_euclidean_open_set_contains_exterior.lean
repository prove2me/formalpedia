-- Prove2me | solution 1 for NoHair.unbounded_euclidean_open_set_contains_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:00:24.3857+00:00
-- url     : https://prove2.me/submissions/774e9dad-a683-4d2e-a2e0-607ad590f6e1

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

private abbrev X := ADMPoint

theorem solution (U : Set ADMPoint) (op : IsOpen U) (unbounded : ¬ Bornology.IsBounded U)
    (boundary : IsCompact (frontier U)) : ∃ R : ℝ, {x : ADMPoint | R < ‖x‖} ⊆ U := by
  classical
  obtain ⟨A,ab⟩ := boundary.isBounded.exists_norm_le
  let R := max A 1
  let E := {x : X | R < ‖x‖}
  have rp : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have rank : 1 < Module.rank ℝ X :=
    Module.one_lt_rank_of_one_lt_finrank (by rw [finrank_euclideanSpace_fin]; decide)
  have sphere := isConnected_sphere rank (0:X) zero_le_one
  have coord : Continuous (fun z : X × ℝ => z.2 • z.1) := continuous_snd.smul continuous_fst
  have domain := sphere.prod (isConnected_Ioi (a:=R))
  have eq : (fun z : X × ℝ => z.2 • z.1) '' (Metric.sphere (0:X) 1 ×ˢ Ioi R) = E := by
    ext x
    constructor
    · rintro ⟨⟨n,t⟩,⟨hn,ht⟩,rfl⟩
      change R < ‖t • n‖
      have nn : ‖n‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hn
      change R<t at ht
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (rp.trans ht),nn,mul_one] using ht
    · intro hx
      change R < ‖x‖ at hx
      have nx := (rp.trans hx).ne'
      refine ⟨(‖x‖⁻¹ • x,‖x‖),⟨?_,hx⟩,?_⟩
      · simp [Metric.mem_sphere,dist_zero_right,norm_smul,nx]
      · change ‖x‖ • (‖x‖⁻¹ • x) = x
        rw [smul_smul,mul_inv_cancel₀ nx,one_smul]
  have connected : IsConnected E := eq ▸ domain.image _ coord.continuousOn
  have dis : Disjoint U (closure U)ᶜ := Set.disjoint_left.mpr fun _ hx h => h (subset_closure hx)
  have covered : E ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases h : x ∈ U
    · exact Or.inl h
    · right; intro cx
      have fr : x ∈ frontier U := by rw [frontier,op.interior_eq]; exact ⟨cx,h⟩
      exact (lt_of_le_of_lt (le_max_left A 1) hx).not_ge (ab x fr)
  rcases connected.isPreconnected.subset_or_subset op isClosed_closure.isOpen_compl dis covered with yes|no
  · exact ⟨R,yes⟩
  · exfalso
    apply unbounded
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R,fun x hx => le_of_not_gt fun far => ?_⟩
    exact (no far) (subset_closure hx)
