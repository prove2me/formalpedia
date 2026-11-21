-- Prove2me | solution 2 for MasulloGRH.frechet_quotient_lifts_precompact
-- status  : ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T23:20:28.815197+00:00
-- url     : https://prove2.me/submissions/33baabe4-b001-446f-9ece-8ad50f1976fb

import Definitions.Def_MasulloGRH_LocallyConvex

open Topology Filter Pointwise


/-- A symmetric `0`-neighbourhood inside a given one, whose double sum stays inside. -/
theorem fq_half {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {s : Set X} (hs : s ∈ 𝓝 (0 : X)) :
    ∃ V ∈ 𝓝 (0 : X), (∀ v ∈ V, -v ∈ V) ∧ (∀ v ∈ V, ∀ w ∈ V, v + w ∈ s) ∧ V ⊆ s := by
  obtain ⟨H, hH, hHs⟩ := exists_nhds_zero_half hs
  have hneg : (fun v : X => -v) ⁻¹' H ∈ 𝓝 (0 : X) := by
    have := (continuous_neg (G := X)).continuousAt (x := 0)
    simpa using this.preimage_mem_nhds (by simpa using hH)
  refine ⟨H ∩ (fun v => -v) ⁻¹' H, inter_mem hH hneg, ?_, ?_, ?_⟩
  · rintro v ⟨h1, h2⟩; exact ⟨h2, by simpa using h1⟩
  · rintro v ⟨hv, -⟩ w ⟨hw, -⟩; exact hHs v hv w hw
  · rintro v ⟨hv, -⟩
    have := hHs v hv 0 (mem_of_mem_nhds hH); simpa using this

/-- A countable basis `V 0 = univ ⊇ V 1 ⊇ ⋯` of symmetric `0`-neighbourhoods with
`V (k+1) + V (k+1) ⊆ V k`. -/
theorem fq_base {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [(𝓝 (0 : X)).IsCountablyGenerated] :
    ∃ V : ℕ → Set X, V 0 = Set.univ ∧ (∀ k, V k ∈ 𝓝 (0 : X)) ∧ (∀ k, ∀ v ∈ V k, -v ∈ V k) ∧
      (∀ k, ∀ v ∈ V (k+1), ∀ w ∈ V (k+1), v + w ∈ V k) ∧
      (∀ U ∈ 𝓝 (0 : X), ∃ k, V k ⊆ U) := by
  obtain ⟨u, hu⟩ := (𝓝 (0 : X)).exists_antitone_basis
  -- choice of a "half" inside `s ∩ u k`
  have hstep : ∀ (k : ℕ) (s : {s : Set X // s ∈ 𝓝 (0 : X)}),
      ∃ V ∈ 𝓝 (0 : X), (∀ v ∈ V, -v ∈ V) ∧ (∀ v ∈ V, ∀ w ∈ V, v + w ∈ s.1) ∧ V ⊆ u k :=
    fun k s => by
      obtain ⟨V, hV, hneg, hadd, hsub⟩ := fq_half (inter_mem s.2 (hu.mem k))
      exact ⟨V, hV, hneg, fun v hv w hw => (hadd v hv w hw).1, fun v hv => (hsub hv).2⟩
  choose nxt hnxt hneg hadd hsub using hstep
  let W : ℕ → {s : Set X // s ∈ 𝓝 (0 : X)} := fun n =>
    Nat.rec ⟨Set.univ, univ_mem⟩ (fun k s => ⟨nxt k s, hnxt k s⟩) n
  refine ⟨fun k => (W k).1, rfl, fun k => (W k).2, ?_, ?_, ?_⟩
  · intro k v hv
    cases k with
    | zero => trivial
    | succ k => exact hneg k (W k) v hv
  · intro k v hv w hw
    exact hadd k (W k) v hv w hw
  · intro U hU
    obtain ⟨k, -, hk⟩ := hu.1.mem_iff.1 hU
    exact ⟨k + 1, (hsub k (W k)).trans hk⟩

/-- Block sums of a sequence with `y j ∈ V j` stay in the earlier neighbourhood. -/
theorem fq_block {X : Type*} [AddCommGroup X] (V : ℕ → Set X)
    (h0 : ∀ k, (0 : X) ∈ V k)
    (hadd : ∀ k, ∀ v ∈ V (k+1), ∀ w ∈ V (k+1), v + w ∈ V k)
    (y : ℕ → X) (hy : ∀ j, y j ∈ V j) :
    ∀ d m, ∑ j ∈ Finset.range d, y (m + 1 + j) ∈ V m := by
  intro d
  induction d with
  | zero => intro m; simpa using h0 m
  | succ d ih =>
    intro m
    rw [Finset.sum_range_succ']
    have h1 := ih (m + 1)
    have : ∑ j ∈ Finset.range d, y (m + 1 + (j + 1)) = ∑ j ∈ Finset.range d, y (m + 1 + 1 + j) := by
      refine Finset.sum_congr rfl fun j _ => by ring_nf
    rw [this, add_comm]
    exact hadd m _ (by simpa using hy (m + 1)) _ h1

theorem fq_closure {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (V : ℕ → Set X) (hV : ∀ k, V k ∈ 𝓝 (0 : X)) (hneg : ∀ k, ∀ v ∈ V k, -v ∈ V k)
    (hadd : ∀ k, ∀ v ∈ V (k+1), ∀ w ∈ V (k+1), v + w ∈ V k) (k : ℕ) :
    closure (V (k+1)) ⊆ V k := by
  intro y hy
  have ht : (fun z : X => z - y) ⁻¹' V (k+1) ∈ 𝓝 y := by
    have hc : ContinuousAt (fun z : X => z - y) y := (continuous_id.sub continuous_const).continuousAt
    exact hc.preimage_mem_nhds (by simpa using hV (k+1))
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff_nhds.1 hy _ ht
  have := hadd k z hz2 (-(z - y)) (hneg _ _ hz1)
  simpa using this

/-- Telescoping: `c (m+1+d) - c (m+1)` is a block sum of increments. -/
theorem fq_tele {X : Type*} [AddCommGroup X] (c : ℕ → X) (m d : ℕ) :
    c (m + 1 + d) - c (m + 1) = ∑ j ∈ Finset.range d, (c (m + 1 + j + 1) - c (m + 1 + j)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ← ih, ← add_assoc]; abel


theorem fq_tail {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (V : ℕ → Set X) (hV : ∀ k, V k ∈ 𝓝 (0 : X)) (hneg : ∀ k, ∀ v ∈ V k, -v ∈ V k)
    (hadd : ∀ k, ∀ v ∈ V (k+1), ∀ w ∈ V (k+1), v + w ∈ V k)
    (c : ℕ → X) (hc : ∀ k, c (k+1) - c k ∈ V k) (s : X) (hs : Tendsto c atTop (𝓝 s)) :
    ∀ m, s - c (m + 2) ∈ V m := by
  have h0 : ∀ k, (0 : X) ∈ V k := fun k => mem_of_mem_nhds (hV k)
  have hblock : ∀ m d, c (m + 1 + d) - c (m + 1) ∈ V m := by
    intro m d
    rw [fq_tele]
    exact fq_block V h0 hadd (fun j => c (j + 1) - c j) hc d m
  intro m
  apply fq_closure V hV hneg hadd m
  have ht : Tendsto (fun d => c (m + 1 + 1 + d) - c (m + 1 + 1)) atTop (𝓝 (s - c (m + 2))) := by
    have : Tendsto (fun d => c (m + 2 + d)) atTop (𝓝 s) :=
      hs.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
    exact this.sub_const _
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun d => hblock (m + 1) d)

theorem fq_converge {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (hX : MasulloGRH.IsCompleteTVS X)
    (V : ℕ → Set X) (hV : ∀ k, V k ∈ 𝓝 (0 : X)) (hneg : ∀ k, ∀ v ∈ V k, -v ∈ V k)
    (hadd : ∀ k, ∀ v ∈ V (k+1), ∀ w ∈ V (k+1), v + w ∈ V k)
    (hbasis : ∀ U ∈ 𝓝 (0 : X), ∃ k, V k ⊆ U)
    (c : ℕ → X) (hc : ∀ k, c (k+1) - c k ∈ V k) :
    ∃ s, Tendsto c atTop (𝓝 s) ∧ ∀ m, s - c (m + 2) ∈ V m := by
  have h0 : ∀ k, (0 : X) ∈ V k := fun k => mem_of_mem_nhds (hV k)
  have hblock : ∀ m d, c (m + 1 + d) - c (m + 1) ∈ V m := by
    intro m d
    rw [fq_tele]
    exact fq_block V h0 hadd (fun j => c (j + 1) - c j) hc d m
  have hcauchy : MasulloGRH.IsCauchyFilter (map c atTop) := by
    refine ⟨inferInstance, fun U hU => ?_⟩
    obtain ⟨k, hk⟩ := hbasis U hU
    refine ⟨c '' Set.Ici (k + 2), ?_, ?_⟩
    · rw [mem_map, mem_atTop_sets]
      exact ⟨k + 2, fun n hn => ⟨n, hn, rfl⟩⟩
    · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show k + 2 ≤ i from hi)
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (show k + 2 ≤ j from hj)
      have h1 := hblock (k + 1) d
      have h2 := hneg _ _ (hblock (k + 1) e)
      have := hadd k _ h1 _ h2
      apply hk
      have e1 : k + 1 + 1 = k + 2 := rfl
      rw [e1] at this
      convert this using 1
      abel
  obtain ⟨s, hs⟩ := hX.2 _ hcauchy
  exact ⟨s, hs, fq_tail V hV hneg hadd c hc s hs⟩

theorem fq_step {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (W : Submodule ℂ X) (R : Set (X ⧸ W))
    (hR : ∀ U ∈ 𝓝 (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), R ⊆ (t : Set (X ⧸ W)) + U)
    (V U : Set X) (hU : U ∈ 𝓝 (0 : X)) (h0V : (0 : X) ∈ V) (hRV : R ⊆ W.mkQ '' V) :
    ∃ F : Finset X, (↑F ⊆ V) ∧ ∀ r ∈ R, ∃ f ∈ F, ∃ u ∈ U, r = W.mkQ (f + u) := by
  classical
  obtain ⟨U', hU', hneg, hadd, -⟩ := fq_half hU
  have hN : W.mkQ '' U' ∈ 𝓝 (0 : X ⧸ W) := by
    simpa using (W.isOpenMap_mkQ).image_mem_nhds (x := 0) hU'
  obtain ⟨t, ht⟩ := hR _ hN
  let P : X ⧸ W → Prop := fun y => ∃ r ∈ R, ∃ u ∈ U', r = y + W.mkQ u
  let g : X ⧸ W → X := fun y =>
    if h : P y then (hRV h.choose_spec.1).choose else 0
  refine ⟨t.image g, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    simp only [g]
    split_ifs with h
    · exact (hRV h.choose_spec.1).choose_spec.1
    · exact h0V
  · intro r hr
    obtain ⟨y, hy, n, ⟨u1, hu1, rfl⟩, hr'⟩ := Set.mem_add.1 (ht hr)
    have hP : P y := ⟨r, hr, u1, hu1, hr'.symm⟩
    refine ⟨g y, Finset.mem_image_of_mem g hy, ?_⟩
    obtain ⟨u2, hu2, hr2⟩ := hP.choose_spec.2
    have hlift := (hRV hP.choose_spec.1).choose_spec.2
    refine ⟨u1 + -u2, hadd _ hu1 _ (hneg _ hu2), ?_⟩
    simp only [g, dif_pos hP]
    rw [map_add, hlift, hr2, map_add, map_neg, ← hr']
    abel


theorem fq_antitone {X : Type*} [AddCommGroup X] (V : ℕ → Set X) (h0 : ∀ k, (0 : X) ∈ V k)
    (hadd : ∀ k, ∀ v ∈ V (k+1), ∀ w ∈ V (k+1), v + w ∈ V k) : ∀ k j, V (k + j) ⊆ V k := by
  intro k j
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    intro v hv
    apply ih
    have := hadd (k + j) v hv 0 (h0 _)
    simpa using this

open MasulloGRH in
theorem solution (X : Type*) [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hF : IsFrechet X) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (B : Set (X ⧸ W))
    (hB : ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U) :
    ∃ S : Set X, (∀ U ∈ nhds (0 : X), ∃ t : Finset X, S ⊆ (t : Set X) + U) ∧
      B ⊆ (W.mkQ : X → X ⧸ W) '' S := by
  classical
  obtain ⟨⟨ι, _, p, hp⟩, hcomp, hmetr⟩ := hF
  haveI := hp.topologicalAddGroup
  haveI := hmetr
  haveI : T2Space (X ⧸ W) := by
    haveI : IsClosed (W.toAddSubgroup : Set X) := hW
    infer_instance
  obtain ⟨V, hV0, hV, hneg, hadd, hbasis⟩ := fq_base (X := X)
  have h0 : ∀ k, (0 : X) ∈ V k := fun k => mem_of_mem_nhds (hV k)
  -- residual sets
  let R : ℕ → Finset X → Set (X ⧸ W) := fun k D =>
    {y | ∃ b ∈ B, ∃ d ∈ D, y = b - W.mkQ d} ∩ W.mkQ '' V k
  have hRpre : ∀ k D, ∀ U ∈ 𝓝 (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), R k D ⊆ (t : Set (X ⧸ W)) + U := by
    intro k D U hU
    obtain ⟨t, ht⟩ := hB U hU
    refine ⟨(t ×ˢ D).image (fun q => q.1 - W.mkQ q.2), ?_⟩
    rintro y ⟨⟨b, hb, d, hd, rfl⟩, -⟩
    obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_add.1 (ht hb)
    refine Set.mem_add.2 ⟨a - W.mkQ d, ?_, u, hu, by abel⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
    exact ⟨(a, d), ⟨ha, hd⟩, rfl⟩
  have hG : ∀ (k : ℕ) (D : Finset X), ∃ F : Finset X, (↑F ⊆ V k) ∧
      ∀ r ∈ R k D, ∃ f ∈ F, ∃ u ∈ V (k+1), r = W.mkQ (f + u) :=
    fun k D => fq_step W (R k D) (hRpre k D) (V k) (V (k+1)) (hV (k+1)) (h0 k)
      (fun y hy => hy.2)
  choose G hGV hGcov using hG
  let D : ℕ → Finset X := fun n => Nat.rec {0} (fun k Dk => Dk + G k Dk) n
  have hDsucc : ∀ k, D (k+1) = D k + G k (D k) := fun k => rfl
  let S : Set X := {s | ∃ c : ℕ → X, (∀ k, c k ∈ D k) ∧ (∀ k, c (k+1) - c k ∈ V k) ∧
    Tendsto c atTop (𝓝 s)}
  refine ⟨S, ?_, ?_⟩
  · -- precompactness
    intro U hU
    obtain ⟨k, hk⟩ := hbasis U hU
    refine ⟨D (k + 2), ?_⟩
    rintro s ⟨c, hcD, hc, hs⟩
    have htail := fq_tail V hV hneg hadd c hc s hs k
    exact Set.mem_add.2 ⟨c (k + 2), hcD _, s - c (k + 2), hk htail, by abel⟩
  · -- lifting
    intro b hb
    let P : ℕ → X → Prop := fun k d => d ∈ D k ∧ b - W.mkQ d ∈ W.mkQ '' V k
    have hP0 : P 0 0 := ⟨by simp [D], by
      rw [hV0, Set.image_univ]; exact Set.mem_range.2 (W.mkQ_surjective _)⟩
    have hnext : ∀ k d, P k d → ∃ d', P (k+1) d' ∧ d' - d ∈ V k := by
      rintro k d ⟨hd, hbd⟩
      obtain ⟨f, hf, u, hu, hr⟩ := hGcov k (D k) (b - W.mkQ d) ⟨⟨b, hb, d, hd, rfl⟩, hbd⟩
      refine ⟨d + f, ⟨?_, ⟨u, hu, ?_⟩⟩, ?_⟩
      · rw [hDsucc]; exact Finset.add_mem_add hd hf
      · rw [map_add] at hr ⊢
        have hb' : b = W.mkQ d + (W.mkQ f + W.mkQ u) := by rw [← hr]; abel
        rw [hb']; abel
      · simpa using hGV k (D k) hf
    choose nxt hnxtP hnxtV using hnext
    let seq : (k : ℕ) → {d : X // P k d} := fun n =>
      Nat.rec ⟨0, hP0⟩ (fun k s => ⟨nxt k s.1 s.2, hnxtP k s.1 s.2⟩) n
    let c : ℕ → X := fun k => (seq k).1
    have hcP : ∀ k, P k (c k) := fun k => (seq k).2
    have hc : ∀ k, c (k+1) - c k ∈ V k := fun k => hnxtV k (seq k).1 (seq k).2
    obtain ⟨s, hs, -⟩ := fq_converge hcomp V hV hneg hadd hbasis c hc
    refine ⟨s, ⟨c, fun k => (hcP k).1, hc, hs⟩, ?_⟩
    -- the images converge to both `mkQ s` and `b`
    have h1 : Tendsto (fun k => W.mkQ (c k)) atTop (𝓝 (W.mkQ s)) :=
      (W.continuous_mkQ.tendsto s).comp hs
    have h2 : Tendsto (fun k => b - W.mkQ (c k)) atTop (𝓝 0) := by
      intro N hN
      have hpre : W.mkQ ⁻¹' N ∈ 𝓝 (0 : X) := by
        have := (W.continuous_mkQ.tendsto (0 : X)) (by simpa using hN)
        exact this
      obtain ⟨k0, hk0⟩ := hbasis _ hpre
      rw [mem_map, mem_atTop_sets]
      refine ⟨k0, fun k hk => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      obtain ⟨v, hv, hveq⟩ := (hcP (k0 + j)).2
      show b - W.mkQ (c (k0 + j)) ∈ N
      rw [← hveq]
      exact hk0 (fq_antitone V h0 hadd k0 j hv)
    have h3 : Tendsto (fun k => W.mkQ (c k)) atTop (𝓝 b) := by
      have := (tendsto_const_nhds (x := b)).sub h2
      simpa using this
    exact tendsto_nhds_unique h1 h3
