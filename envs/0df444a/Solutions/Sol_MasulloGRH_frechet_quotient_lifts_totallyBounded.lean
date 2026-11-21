-- Prove2me | solution 1 for MasulloGRH.frechet_quotient_lifts_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:01:58.415965+00:00
-- url     : https://prove2.me/submissions/654bac2c-8d95-4f76-945d-49cb145db260

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open Set Filter Topology MasulloGRH
open scoped Uniformity Pointwise

private theorem complete_of_cauchy_filters (X : Type*) [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] (h : IsCompleteTVS X) : CompleteSpace X := by
  constructor
  intro f hf
  apply h.2 f
  refine ⟨hf.1, ?_⟩
  intro U hU
  have hrel : {p : X × X | p.2 - p.1 ∈ U} ∈ 𝓤 X := by
    rw [uniformity_eq_comap_nhds_zero]
    exact preimage_mem_comap hU
  obtain ⟨S, hS, hd⟩ := (cauchy_iff.mp hf).2 _ hrel
  exact ⟨S, hS, fun x hx y hy => hd (show (y,x) ∈ S ×ˢ S from ⟨hy,hx⟩)⟩

-- A finite net is chosen at each scale. Lift its successive differences by
-- one fixed section at that scale, so the lifted approximants have finite range.
private theorem totallyBounded_lift {X Y : Type*}
    [AddCommGroup X] [MetricSpace X] [IsUniformAddGroup X] [CompleteSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    (q : X →+ Y) (hq : Continuous q) (ho : IsOpenMap q) (hs : Function.Surjective q)
    (B : Set Y) (hB : ∀ U ∈ 𝓝 (0 : Y), ∃ t : Finset Y, B ⊆ (t : Set Y) + U) :
    ∃ K : Set X, TotallyBounded K ∧ B ⊆ q '' K := by
  classical
  let δ (n : ℕ) : ℝ := (1 / 2 : ℝ)^n
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hsmall (n : ℕ) : ∃ V ∈ 𝓝 (0 : X),
      ∀ x : X, ∀ v ∈ V, dist x (x + v) < δ n := by
    have hm := Metric.dist_mem_uniformity (α := X) (hδ n)
    rw [uniformity_eq_comap_nhds_zero] at hm
    obtain ⟨V,hV,h⟩ := mem_comap.mp hm
    exact ⟨V,hV,fun x v hv => h (a := (x,x+v)) (by simpa using hv)⟩
  choose V hV hmove using hsmall
  have qnhds (S : Set X) (h : S ∈ 𝓝 0) : q '' S ∈ 𝓝 0 := by
    simpa only [map_zero] using ho.image_mem_nhds h
  have shrink (n : ℕ) : ∃ R ∈ 𝓝 (0 : Y), ∀ a ∈ R, ∀ b ∈ R, a-b ∈ q '' V n := by
    have hsub : Continuous (fun p : Y × Y => p.1 - p.2) := continuous_fst.sub continuous_snd
    have H := hsub.tendsto (0,0)
    change Tendsto _ _ (𝓝 ((0:Y)-0)) at H
    rw [sub_self] at H
    obtain ⟨R,hR,S,hS,h⟩ := mem_nhds_prod_iff.mp (H (qnhds _ (hV n)))
    exact ⟨R ∩ S, inter_mem hR hS, fun a ha b hb =>
      h (show (a,b) ∈ R ×ˢ S from ⟨ha.1,hb.2⟩)⟩
  choose R hR hsub using shrink
  let U (n : ℕ) := (R n ∩ R (n-1)) ∩ q '' Metric.ball 0 (δ n)
  have hU (n : ℕ) : U n ∈ 𝓝 0 :=
    inter_mem (inter_mem (hR _) (hR _)) (qnhds _ (Metric.ball_mem_nhds _ (hδ n)))
  choose T hT using fun n => hB (U n) (hU n)
  have net (n : ℕ) (b : B) : ∃ c ∈ T n, (b:Y) - c ∈ U n := by
    obtain ⟨c,hc,e,he,hce⟩ := hT n b.property
    exact ⟨c,hc,by rw [← hce]; simpa using he⟩
  choose c hc herr using net
  have hcfin (n : ℕ) : (range (c n)).Finite :=
    (T n).finite_toSet.subset (by rintro _ ⟨b,rfl⟩; exact hc n b)
  let diff (n : ℕ) (b : B) := c (n+1) b - c n b
  have hdiff (n : ℕ) (b : B) : diff n b ∈ q '' V n := by
    have H := hsub n _ (herr n b).1.1 _ (show (b:Y)-c (n+1) b ∈ R n by
      simpa using (herr (n+1) b).1.2)
    convert H using 1
    dsimp [diff]
    abel
  let step (n : ℕ) (d : Y) : X := if h : d ∈ q '' V n then h.choose else 0
  have hstep (n : ℕ) (b : B) :
      step n (diff n b) ∈ V n ∧ q (step n (diff n b)) = diff n b := by
    simpa only [step, dif_pos (hdiff n b)] using (hdiff n b).choose_spec
  let start (y : Y) := (hs y).choose
  let x : ℕ → B → X := Nat.rec (fun b => start (c 0 b))
    (fun n prev b => prev b + step n (diff n b))
  have hqx (n : ℕ) (b : B) : q (x n b) = c n b := by
    induction n with
    | zero => exact (hs _).choose_spec
    | succ n ih =>
      change q (x n b + step n (diff n b)) = _
      rw [map_add, ih, (hstep n b).2]
      dsimp [diff]
      abel
  have hxfin (n : ℕ) : (range (x n)).Finite := by
    induction n with
    | zero => exact ((hcfin 0).image start).subset (by rintro _ ⟨b,rfl⟩; exact ⟨_,⟨b,rfl⟩,rfl⟩)
    | succ n ih =>
      have hd : (range (diff n)).Finite := ((hcfin (n+1)).sub (hcfin n)).subset
        (by rintro _ ⟨b,rfl⟩; exact ⟨_,⟨b,rfl⟩,_,⟨b,rfl⟩,rfl⟩)
      exact (ih.add (hd.image (step n))).subset (by
        rintro _ ⟨b,rfl⟩; exact ⟨_,⟨b,rfl⟩,_,⟨_,⟨b,rfl⟩,rfl⟩,rfl⟩)
  have hdist (b : B) (n : ℕ) : dist (x n b) (x (n+1) b) ≤ 1 * (1/2 : ℝ)^n := by
    simpa only [one_mul] using (hmove n (x n b) _ (hstep n b).1).le
  choose l hl using fun b => cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) 1 (by norm_num) (hdist b))
  refine ⟨range l, Metric.totallyBounded_iff.mpr ?_, ?_⟩
  · intro ε hε
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (show (1/2:ℝ) < 1 by norm_num)
    refine ⟨range (x n), hxfin n, ?_⟩
    rintro _ ⟨b,rfl⟩
    refine mem_iUnion.mpr ⟨x n b, mem_iUnion.mpr ⟨⟨b,rfl⟩, ?_⟩⟩
    rw [Metric.mem_ball, dist_comm]
    have H := dist_le_of_le_geometric_of_tendsto (1/2) 1 (by norm_num) (hdist b) (hl b) n
    norm_num at H
    linarith
  · intro y hy
    let b : B := ⟨y,hy⟩
    have hlimδ : Tendsto δ atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    choose e he hqe using fun n => (herr n b).2
    have hlim : Tendsto e atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun _ => dist_nonneg) (fun n => (he n).le) hlimδ)
    have hq0 : Tendsto (fun n => q (e n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, map_zero] using (hq.tendsto 0).comp hlim
    have hc' : Tendsto (fun n => c n b) atTop (𝓝 y) := by
      have H : Tendsto (fun n => y - q (e n)) atTop (𝓝 (y-0)) := tendsto_const_nhds.sub hq0
      simpa only [hqe, sub_sub_cancel, sub_zero, b] using H
    have hxq := (hq.tendsto (l b)).comp (hl b)
    refine ⟨l b, ⟨b,rfl⟩, tendsto_nhds_unique ?_ hc'⟩
    simpa only [Function.comp_def, hqx] using hxq

theorem solution (X : Type*) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hF : IsFrechet X) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (B : Set (X ⧸ W))
    (hB : ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U) :
    ∃ B' : Set X, Bornology.IsVonNBounded ℂ B' ∧ B ⊆ (W.mkQ : X → X ⧸ W) '' B' := by
  obtain ⟨_, _, p, hp⟩ := hF.1
  let := hp.topologicalAddGroup
  let := hp.continuousSMul
  let := hF.2.1.1
  let := hF.2.2
  let := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let := complete_of_cauchy_filters X hF.2.1
  let : (𝓤 X).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let := UniformSpace.metricSpace X
  let : IsClosed (W.toAddSubgroup : Set X) := hW
  let : T2Space (X ⧸ W) := QuotientAddGroup.instT2Space
  obtain ⟨K,hK,hBK⟩ := totallyBounded_lift W.mkQ.toAddMonoidHom W.continuous_mkQ
    W.isOpenMap_mkQ W.mkQ_surjective B hB
  exact ⟨K,hK.isVonNBounded ℂ,hBK⟩
