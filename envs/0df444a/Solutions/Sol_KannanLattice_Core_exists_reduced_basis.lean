-- Prove2me | solution 1 for KannanLattice.Core.exists_reduced_basis
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:58:16.357903+00:00
-- url     : https://prove2.me/submissions/3fa35a49-6d70-4302-a9df-39d963cce873

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced



namespace KannanLattice.Core

open InnerProductSpace

lemma kz_lls {ι : Type*} {k : ℕ} (b : ι → EuclideanSpace ℝ (Fin k))
    {v : EuclideanSpace ℝ (Fin k)} (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    v ∈ Submodule.span ℝ (Set.range b) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ hx

theorem kz_prim {ι : Type*} [Fintype ι] (k : ℕ)
    (b : ι → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (v : EuclideanSpace ℝ (Fin k)) (hv : v ∈ Submodule.span ℤ (Set.range b)) (hv0 : v ≠ 0)
    (hprim : ∀ t : ℝ, 0 < t → t < 1 → t • v ∉ Submodule.span ℤ (Set.range b)) :
    ∃ b' : ι → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ Submodule.span ℤ (Set.range b') = Submodule.span ℤ (Set.range b) ∧ v ∈ Set.range b' := by
  classical
  have hbZ : LinearIndependent ℤ b := hb.restrict_scalars' ℤ
  let b0 : Module.Basis (ι) ℤ (Submodule.span ℤ (Set.range b)) := Module.Basis.span hbZ
  let v' : Submodule.span ℤ (Set.range b) := ⟨v, hv⟩
  let N : Submodule ℤ (Submodule.span ℤ (Set.range b)) := Submodule.span ℤ {v'}
  obtain ⟨n, S⟩ := Submodule.smithNormalForm b0 N
  have hv'N : v' ∈ N := Submodule.mem_span_singleton_self _
  have hn : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    have := S.bN.repr.injective (a₁ := ⟨v', hv'N⟩) (a₂ := 0) (Subsingleton.elim _ _)
    apply hv0
    have := congrArg (fun x : N => ((x : Submodule.span ℤ (Set.range b)) : EuclideanSpace ℝ (Fin k))) this
    simpa [v'] using this
  let i0 : Fin n := ⟨0, hn⟩
  set e : Submodule.span ℤ (Set.range b) := S.bM (S.f i0) with he
  have hsnf := S.snf i0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (S.bN i0).2
  have hne : (S.bN i0 : Submodule.span ℤ (Set.range b)) ≠ 0 := by
    intro h; apply S.bN.ne_zero i0; exact Subtype.ext h
  have hE : c • v = S.a i0 • (e : EuclideanSpace ℝ (Fin k)) := by
    have := congrArg (fun x : Submodule.span ℤ (Set.range b) => (x : EuclideanSpace ℝ (Fin k))) (hc.trans hsnf)
    simpa [v'] using this
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hne; rw [← hc, zero_smul]
  have ha0 : S.a i0 ≠ 0 := by
    intro h0; rw [h0, zero_smul, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_zero] at hE
    rcases hE with h | h
    · exact hc0 (by exact_mod_cast h)
    · exact hv0 h
  -- the real multiples of v in the lattice are integer multiples
  have hint : ∀ t : ℝ, t • v ∈ Submodule.span ℤ (Set.range b) → ∃ q : ℤ, t = q := by
    intro t ht
    refine ⟨⌊t⌋, ?_⟩
    by_contra hne'
    have h1 : 0 < t - ⌊t⌋ := by
      have := Int.floor_le t
      exact lt_of_le_of_ne (by linarith) (fun h => hne' (by linarith))
    have h2 : t - ⌊t⌋ < 1 := by linarith [Int.lt_floor_add_one t]
    apply hprim _ h1 h2
    rw [sub_smul]
    refine Submodule.sub_mem _ ht ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ hv
  have heR : (e : EuclideanSpace ℝ (Fin k)) = ((c : ℝ) / (S.a i0 : ℝ)) • v := by
    have hE' : (c : ℝ) • v = (S.a i0 : ℝ) • (e : EuclideanSpace ℝ (Fin k)) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact hE
    have ha0' : (S.a i0 : ℝ) ≠ 0 := by exact_mod_cast ha0
    rw [div_eq_mul_inv, mul_comm, mul_smul, hE', smul_smul, inv_mul_cancel₀ ha0', one_smul]
  obtain ⟨q, hq⟩ := hint _ (by rw [← heR]; exact e.2)
  have heq : e = q • v' := by
    apply Subtype.ext
    rw [heR, hq]
    simp [v', Int.cast_smul_eq_zsmul]
  have hq1 : q = 1 ∨ q = -1 := by
    have h := congrArg (fun x => S.bM.repr x (S.f i0)) heq
    simp only [he, Module.Basis.repr_self, Finsupp.single_eq_same, map_zsmul,
      Finsupp.smul_apply, smul_eq_mul] at h
    exact Int.eq_one_or_neg_one_of_mul_eq_one h.symm
  have hve : v = q • (e : EuclideanSpace ℝ (Fin k)) := by
    have : (e : EuclideanSpace ℝ (Fin k)) = q • v := by rw [heq]; simp [v']
    rw [this, smul_smul]
    rcases hq1 with rfl | rfl <;> simp
  let b' : ι → EuclideanSpace ℝ (Fin k) :=
    fun j => if j = S.f i0 then v else (S.bM j : EuclideanSpace ℝ (Fin k))
  have hb'mem : ∀ j, b' j ∈ Submodule.span ℤ (Set.range b) := by
    intro j; simp only [b']; split_ifs
    · exact hv
    · exact (S.bM j).2
  have hbMmem : ∀ j, (S.bM j : EuclideanSpace ℝ (Fin k)) ∈ Submodule.span ℤ (Set.range b') := by
    intro j
    by_cases hj : j = S.f i0
    · subst hj
      have : (S.bM (S.f i0) : EuclideanSpace ℝ (Fin k)) = q • b' (S.f i0) := by
        simp only [b', if_pos rfl]
        rw [hve, smul_smul]
        rcases hq1 with rfl | rfl <;> simp [he]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have : (S.bM j : EuclideanSpace ℝ (Fin k)) = b' j := by simp [b', hj]
      rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
  have hlat : Submodule.span ℤ (Set.range b') = Submodule.span ℤ (Set.range b) := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hb'mem j)
    · intro x hx
      have := S.bM.sum_repr ⟨x, hx⟩
      have hx' : x = ∑ j, S.bM.repr ⟨x, hx⟩ j • (S.bM j : EuclideanSpace ℝ (Fin k)) := by
        have h2 : ((∑ j, S.bM.repr ⟨x, hx⟩ j • S.bM j : Submodule.span ℤ (Set.range b)) : EuclideanSpace ℝ (Fin k))
            = x := by rw [this]
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul_of_tower] at h2
        exact h2.symm
      rw [hx']
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbMmem j)
  have hspan : Submodule.span ℝ (Set.range b') = Submodule.span ℝ (Set.range b) := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact kz_lls b (hb'mem j))
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      apply kz_lls b'
      rw [hlat]
      exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨b', ?_, hlat, ⟨S.f i0, by simp [b']⟩⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  have := (linearIndependent_iff_card_eq_finrank_span.1 hb)
  rw [this]
  unfold Set.finrank
  rw [hspan]

lemma kz_gs_mem_orth {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (j : Fin m) :
    gramSchmidt ℝ b j ∈ (Submodule.span ℝ (b '' Set.Iio j))ᗮ := by
  rw [← span_gramSchmidt_Iio ℝ b j, Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact gramSchmidt_orthogonal ℝ b (ne_of_lt hi)
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

lemma kz_gs_eq {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (j : Fin m) :
    gramSchmidt ℝ b j = projOrth b j (b j) := by
  have hs : (∑ i ∈ Finset.Iio j, (ℝ ∙ gramSchmidt ℝ b i).starProjection (b j)) ∈
      Submodule.span ℝ (b '' Set.Iio j) := by
    rw [← span_gramSchmidt_Iio ℝ b j]
    refine Submodule.sum_mem _ fun i hi => ?_
    have h1 : (ℝ ∙ gramSchmidt ℝ b i) ≤ Submodule.span ℝ (gramSchmidt ℝ b '' Set.Iio j) :=
      Submodule.span_mono (Set.singleton_subset_iff.2 ⟨i, Finset.mem_Iio.1 hi, rfl⟩)
    exact h1 (Submodule.starProjection_apply_mem _ _)
  conv_rhs => rw [gramSchmidt_def' ℝ b j]
  unfold projOrth
  rw [map_add, Submodule.starProjection_orthogonal_apply_eq_zero hs, add_zero,
    (Submodule.starProjection_eq_self_iff).2 (kz_gs_mem_orth b j)]

lemma kz_projOrth_congr {m k : ℕ} (b c : Fin m → EuclideanSpace ℝ (Fin k)) (j : Fin m)
    (h : ∀ i < j, b i = c i) : projOrth b j = projOrth c j := by
  unfold projOrth
  have : b '' Set.Iio j = c '' Set.Iio j := Set.image_congr (fun i hi => h i hi)
  simp only [this]

lemma kz_gs_congr {m k : ℕ} (b c : Fin m → EuclideanSpace ℝ (Fin k)) (j : Fin m)
    (h : ∀ i ≤ j, b i = c i) : gramSchmidt ℝ b j = gramSchmidt ℝ c j := by
  rw [kz_gs_eq, kz_gs_eq, kz_projOrth_congr b c j (fun i hi => h i hi.le), h j le_rfl]

lemma kz_li_of_lattice {m k : ℕ} (b c : Fin m → EuclideanSpace ℝ (Fin k))
    (hb : LinearIndependent ℝ b) (hlat : lattice c = lattice b) : LinearIndependent ℝ c := by
  have hspan : Submodule.span ℝ (Set.range c) = Submodule.span ℝ (Set.range b) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      apply kz_lls b
      change c j ∈ lattice b
      rw [← hlat]
      exact Submodule.subset_span ⟨j, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      apply kz_lls c
      change b j ∈ lattice c
      rw [hlat]
      exact Submodule.subset_span ⟨j, rfl⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  have := (linearIndependent_iff_card_eq_finrank_span.1 hb)
  simp only [this]
  unfold Set.finrank
  rw [hspan]

lemma kz_finite {ι : Type*} [Fintype ι] {k : ℕ} (c : ι → EuclideanSpace ℝ (Fin k))
    (hc : LinearIndependent ℝ c) (R : ℝ) :
    {x | x ∈ Submodule.span ℤ (Set.range c) ∧ ‖x‖ ≤ R}.Finite := by
  let F := Submodule.span ℝ (Set.range c)
  let bF := Module.Basis.span hc
  have hfin := ZSpan.setFinite_inter bF (s := Metric.closedBall (0:F) R) Metric.isBounded_closedBall
  refine (hfin.image Subtype.val).subset ?_
  rintro x ⟨hx, hxR⟩
  obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  have hcoe : ((∑ i, n i • bF i : F) : EuclideanSpace ℝ (Fin k)) = ∑ i, n i • c i := by
    simp [bF, Module.Basis.span_apply]
  refine ⟨∑ i, n i • bF i, ⟨?_, ?_⟩, hcoe⟩
  · rw [Metric.mem_closedBall, dist_zero_right, ← Submodule.norm_coe, hcoe]; exact hxR
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma projOrth_eq_zero_of_mem {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (i : Fin m)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ Submodule.span ℝ (b '' Set.Iio i)) :
    projOrth b i x = 0 := by
  unfold projOrth
  exact Submodule.starProjection_orthogonal_apply_eq_zero hx
lemma projOrth_tail_ne_zero {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    (hb : LinearIndependent ℝ b) (i : Fin m) (ν : {j : Fin m // i ≤ j} → ℝ) (hν : ν ≠ 0) :
    projOrth b i (∑ j : {j : Fin m // i ≤ j}, ν j • b j) ≠ 0 := by
  intro h
  unfold projOrth at h
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h
  have h2 : (∑ j : {j : Fin m // i ≤ j}, ν j • b j) ∈ Submodule.span ℝ (b '' Set.Ici i) := by
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨j, Set.mem_Ici.2 j.2, rfl⟩
  have hdisj := hb.disjoint_span_image (s := Set.Iio i) (t := Set.Ici i)
    (Set.disjoint_left.2 fun x hx hx' => absurd (Set.mem_Ici.1 hx') (not_le.2 (Set.mem_Iio.1 hx)))
  have h0 := (Submodule.disjoint_def.1 hdisj) _ h h2
  have hli : LinearIndependent ℝ (fun j : {j : Fin m // i ≤ j} => b j) :=
    hb.comp _ Subtype.val_injective
  apply hν
  funext j
  exact Fintype.linearIndependent_iff.1 hli ν h0 j


theorem kz_step {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (t : Fin m) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k), LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧
      (∀ i < t, b' i = b i) ∧ gsLen b' t = lambdaOne (projLattice b' t) := by
  classical
  set P := projOrth b t with hP
  let c : {i : Fin m // t ≤ i} → EuclideanSpace ℝ (Fin k) := fun i => P (b i)
  have hc : LinearIndependent ℝ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hne
    apply projOrth_tail_ne_zero b hb t g (fun h => hne (by simp [h]))
    rw [map_sum]
    simpa [map_smul, c] using hg
  have hPlow : ∀ i : Fin m, i < t → P (b i) = 0 := fun i hi =>
    projOrth_eq_zero_of_mem b t (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hfwd : ∀ x ∈ lattice b, P x ∈ Submodule.span ℤ (Set.range c) := by
    intro x hx
    unfold lattice at hx
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    rw [map_sum, ← Fintype.sum_subtype_add_sum_subtype (fun i => t ≤ i)
      (fun i => P (n i • b i))]
    have h0 : ∑ i : {i : Fin m // ¬ t ≤ i}, P (n i • b i) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [map_zsmul, hPlow i (not_le.1 i.2), smul_zero])
    rw [h0, add_zero]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_zsmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hbwd : ∀ y ∈ Submodule.span ℤ (Set.range c), ∃ x ∈ lattice b, P x = y := by
    intro y hy
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
    refine ⟨∑ i, n i • b i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rw [map_sum]
    simp only [map_zsmul, c]
  let t0 : {i : Fin m // t ≤ i} := ⟨t, le_rfl⟩
  have hct0 : c t0 ≠ 0 := by
    change P (b t) ≠ 0
    rw [hP, ← kz_gs_eq]; exact gramSchmidt_ne_zero t hb
  set S := {x | x ∈ Submodule.span ℤ (Set.range c) ∧ ‖x‖ ≤ ‖c t0‖} \ {0} with hS
  have hSfin : S.Finite := (kz_finite c hc _).subset Set.sdiff_subset
  have hSne : S.Nonempty := ⟨c t0, ⟨Submodule.subset_span ⟨t0, rfl⟩, le_rfl⟩, hct0⟩
  obtain ⟨w, hwS, hwmin⟩ := Set.exists_min_image S (fun x => ‖x‖) hSfin hSne
  have hwL : w ∈ Submodule.span ℤ (Set.range c) := hwS.1.1
  have hw0 : w ≠ 0 := hwS.2
  have hmin : ∀ y ∈ Submodule.span ℤ (Set.range c), y ≠ 0 → ‖w‖ ≤ ‖y‖ := by
    intro y hy hy0
    by_cases hle : ‖y‖ ≤ ‖c t0‖
    · exact hwmin y ⟨⟨hy, hle⟩, hy0⟩
    · exact le_trans hwS.1.2 (le_of_lt (not_le.1 hle))
  have hprim : ∀ r : ℝ, 0 < r → r < 1 → r • w ∉ Submodule.span ℤ (Set.range c) := by
    intro r hr0 hr1 hmem
    have h1 := hmin _ hmem (smul_ne_zero hr0.ne' hw0)
    rw [norm_smul, Real.norm_of_nonneg hr0.le] at h1
    have : 0 < ‖w‖ := norm_pos_iff.2 hw0
    nlinarith
  obtain ⟨c', hc'li, hc'lat, i0, hi0⟩ := kz_prim k c hc w hwL hw0 hprim
  let c'' := c' ∘ Equiv.swap t0 i0
  have hc''t0 : c'' t0 = w := by simp [c'', hi0]
  have hc''lat : Submodule.span ℤ (Set.range c'') = Submodule.span ℤ (Set.range c) := by
    rw [← hc'lat]
    congr 1
    exact EquivLike.range_comp c' _
  have hlift : ∀ i, ∃ x ∈ lattice b, P x = c'' i := fun i =>
    hbwd _ (hc''lat ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose e he hPe using hlift
  let b' : Fin m → EuclideanSpace ℝ (Fin k) := fun i => if h : t ≤ i then e ⟨i, h⟩ else b i
  have hb'lo : ∀ i < t, b' i = b i := fun i hi => by simp [b', not_le.2 hi]
  have hb'e : ∀ i : {i : Fin m // t ≤ i}, b' i = e i := fun i => by simp [b', i.2]
  have hb'mem : ∀ i, b' i ∈ lattice b := by
    intro i
    by_cases h : t ≤ i
    · simp only [b', dif_pos h]; exact he _
    · rw [hb'lo i (not_le.1 h)]; exact Submodule.subset_span ⟨i, rfl⟩
  have hbmem : ∀ j, b j ∈ lattice b' := by
    intro j
    by_cases hj : t ≤ j
    · have h1 : P (b j) ∈ Submodule.span ℤ (Set.range c'') := by
        rw [hc''lat]; exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h1
      have hzmem : (∑ i, n i • e i) ∈ lattice b' := Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (by rw [← hb'e i]; exact Submodule.subset_span ⟨_, rfl⟩)
      have hPz : P (∑ i, n i • e i) = P (b j) := by
        rw [map_sum, ← hn]; simp only [map_zsmul, hPe]
      have hyL : b j - ∑ i, n i • e i ∈ lattice b :=
        Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
          (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i))
      have hPy : P (b j - ∑ i, n i • e i) = 0 := by rw [map_sub, hPz, sub_self]
      have hyW : b j - ∑ i, n i • e i ∈ Submodule.span ℝ (b '' Set.Iio t) := by
        rw [hP] at hPy; unfold projOrth at hPy
        rwa [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at hPy
      unfold lattice at hyL
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hyL
      have hAB : b j - ∑ i, n i • e i = (∑ i : {i : Fin m // t ≤ i}, a i • b i) +
          ∑ i : {i : Fin m // ¬ t ≤ i}, a i • b i := by
        rw [← ha]; exact (Fintype.sum_subtype_add_sum_subtype _ _).symm
      have hAW : (∑ i : {i : Fin m // ¬ t ≤ i}, a i • b i) ∈ Submodule.span ℝ (b '' Set.Iio t) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _
          (Submodule.subset_span ⟨i, not_le.1 i.2, rfl⟩)
      have hBW : (∑ i : {i : Fin m // t ≤ i}, a i • b i) ∈ Submodule.span ℝ (b '' Set.Iio t) := by
        have : (∑ i : {i : Fin m // t ≤ i}, a i • b i) = (b j - ∑ i, n i • e i) -
            ∑ i : {i : Fin m // ¬ t ≤ i}, a i • b i := by rw [hAB]; abel
        rw [this]; exact Submodule.sub_mem _ hyW hAW
      have hBW' : (∑ i : {i : Fin m // t ≤ i}, a i • b i) ∈ Submodule.span ℝ (b '' Set.Ici t) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _
          (Submodule.subset_span ⟨i, Set.mem_Ici.2 i.2, rfl⟩)
      have hdisj := hb.disjoint_span_image (s := Set.Iio t) (t := Set.Ici t)
        (Set.disjoint_left.2 fun x hx hx' => absurd (Set.mem_Ici.1 hx') (not_le.2 (Set.mem_Iio.1 hx)))
      have hB0 := (Submodule.disjoint_def.1 hdisj) _ hBW hBW'
      have hAmem : (∑ i : {i : Fin m // ¬ t ≤ i}, a i • b i) ∈ lattice b' :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (by rw [← hb'lo i (not_le.1 i.2)]; exact Submodule.subset_span ⟨_, rfl⟩)
      have : b j = (∑ i : {i : Fin m // ¬ t ≤ i}, a i • b i) + ∑ i, n i • e i := by
        have h2 : b j = (b j - ∑ i, n i • e i) + ∑ i, n i • e i := by abel
        rw [h2, hAB, hB0, zero_add]
      rw [this]; exact add_mem hAmem hzmem
    · rw [← hb'lo j (not_le.1 hj)]; exact Submodule.subset_span ⟨j, rfl⟩
  have hlat : lattice b' = lattice b :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb'mem i))
      (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbmem i))
  have hP' : projOrth b' t = P := kz_projOrth_congr b' b t hb'lo
  refine ⟨b', kz_li_of_lattice b b' hb hlat, hlat, hb'lo, ?_⟩
  have hgs : gsLen b' t = ‖w‖ := by
    have : b' t = e t0 := hb'e t0
    unfold gsLen; rw [kz_gs_eq, hP', this, hPe, hc''t0]
  have hlam : lambdaOne (projLattice b' t) = ‖w‖ := by
    unfold lambdaOne projLattice
    rw [hP', hlat]
    apply IsLeast.csInf_eq
    constructor
    · obtain ⟨x, hx, hPx⟩ := hbwd w hwL
      exact ⟨w, ⟨⟨x, hx, hPx⟩, hw0⟩, rfl⟩
    · rintro _ ⟨y, ⟨⟨x, hx, rfl⟩, hy0⟩, rfl⟩
      exact hmin _ (hfwd x hx) (by simpa using hy0)
  rw [hgs, hlam]

lemma inner_gsN_lt {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) {t j : Fin m}
    (h : t < j) : inner ℝ (gramSchmidtNormed ℝ b j) (b t) = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, gramSchmidt_inv_triangular ℝ b h]

lemma inner_gs_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidt ℝ b t) (b t) = ‖gramSchmidt ℝ b t‖ ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' ℝ b t]
  rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [inner_smul_right, gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.1 hi).ne', mul_zero]

lemma inner_gsN_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidtNormed ℝ b t) (b t) = gsLen b t := by
  unfold gramSchmidtNormed gsLen
  rw [inner_smul_left, inner_gs_self]
  simp only [RCLike.conj_to_real]
  by_cases h : ‖gramSchmidt ℝ b t‖ = 0
  · simp [h]
  · field_simp
    rfl

lemma gsLen_pos {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (t : Fin m) : 0 < gsLen b t := by
  unfold gsLen
  exact norm_pos_iff.2 (gramSchmidt_ne_zero t hb)


theorem kz_partial {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∀ s ≤ m, ∃ b' : Fin m → EuclideanSpace ℝ (Fin k), LinearIndependent ℝ b' ∧
      lattice b' = lattice b ∧ ∀ j : Fin m, (j : ℕ) < s → gsLen b' j = lambdaOne (projLattice b' j) := by
  intro s
  induction s with
  | zero => intro _; exact ⟨b, hb, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ s ih =>
    intro hs
    obtain ⟨b1, hb1, hl1, h1⟩ := ih (by omega)
    obtain ⟨b2, hb2, hl2, hlo, hst⟩ := kz_step b1 hb1 ⟨s, by omega⟩
    refine ⟨b2, hb2, hl2.trans hl1, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · have hjt : j < (⟨s, by omega⟩ : Fin m) := hj
      have hg : gsLen b2 j = gsLen b1 j := by
        unfold gsLen
        rw [kz_gs_congr b2 b1 j (fun i hi => hlo i (lt_of_le_of_lt hi hjt))]
      have hp : projLattice b2 j = projLattice b1 j := by
        unfold projLattice
        rw [kz_projOrth_congr b2 b1 j (fun i hi => hlo i (lt_trans hi hjt)), hl2]
      rw [hg, hp]; exact h1 j hj
    · have : j = ⟨s, by omega⟩ := Fin.ext hj
      rw [this]; exact hst

lemma kz_near {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (i : Fin m) (x : EuclideanSpace ℝ (Fin k)) :
    ∃ y ∈ Submodule.span ℤ (b '' Set.Iio i), ∀ j < i,
      |inner ℝ (gramSchmidtNormed ℝ b j) (x - y)| ≤ gsLen b j / 2 := by
  set u := gramSchmidtNormed ℝ b with hu
  have key : ∀ s, s ≤ (i : ℕ) → ∃ y ∈ Submodule.span ℤ (b '' Set.Iio i), ∀ j < i,
      (i : ℕ) - s ≤ (j : ℕ) → |inner ℝ (u j) (x - y)| ≤ gsLen b j / 2 := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨0, Submodule.zero_mem _, fun j hj hj' => ?_⟩
      exfalso; have : (j : ℕ) < i := hj; omega
    | succ s ih =>
      intro hs
      obtain ⟨y, hy, hyj⟩ := ih (by omega)
      set t : Fin m := ⟨i - s - 1, by omega⟩ with ht
      have hti : t < i := by rw [Fin.lt_def]; simp [ht]; omega
      have hpos := gsLen_pos b hb t
      set z := inner ℝ (u t) (x - y) / gsLen b t with hz
      refine ⟨y + round z • b t, ?_, ?_⟩
      · exact Submodule.add_mem _ hy (Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, hti, rfl⟩))
      · intro j hj hj'
        have e : x - (y + round z • b t) = (x - y) - ((round z : ℤ) : ℝ) • b t := by
          rw [Int.cast_smul_eq_zsmul]; abel
        rw [e, inner_sub_right, inner_smul_right]
        rcases (show (j : ℕ) = i - s - 1 ∨ i - s ≤ (j : ℕ) by omega) with h1 | h1
        · have : j = t := Fin.ext h1
          rw [this, hu, inner_gsN_self, ← hu]
          have h2 : inner ℝ (u t) (x - y) = z * gsLen b t := by
            rw [hz]; field_simp
          rw [h2, ← sub_mul, abs_mul, abs_of_pos hpos]
          have := abs_sub_round z
          nlinarith
        · have hlt : t < j := by
            rw [Fin.lt_def]; simp [ht]; omega
          rw [hu, inner_gsN_lt b hlt, ← hu, mul_zero, sub_zero]
          exact hyj j hj h1
  obtain ⟨y, hy, hyj⟩ := key i le_rfl
  exact ⟨y, hy, fun j hj => hyj j hj (by omega)⟩

theorem kz_core (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ IsReduced b' := by
  classical
  obtain ⟨b1, hb1, hl1, h1⟩ := kz_partial b hb m le_rfl
  choose y hy hyb using fun i => kz_near b1 hb1 i (b1 i)
  let b2 : Fin m → EuclideanSpace ℝ (Fin k) := fun i => b1 i - y i
  -- prefix spans agree
  have hle : ∀ i, Submodule.span ℤ (b2 '' Set.Iio i) ≤ Submodule.span ℤ (b1 '' Set.Iio i) := by
    intro i
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨l, hl, rfl⟩) ?_
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hl))) (hy l)
  have hge : ∀ n : ℕ, ∀ i : Fin m, (i : ℕ) = n →
      Submodule.span ℤ (b1 '' Set.Iio i) ≤ Submodule.span ℤ (b2 '' Set.Iio i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      refine Submodule.span_le.2 ?_
      rintro _ ⟨l, hl, rfl⟩
      have : b1 l = b2 l + y l := by simp [b2]
      rw [SetLike.mem_coe, this]
      refine Submodule.add_mem _ (Submodule.subset_span ⟨l, hl, rfl⟩) ?_
      have hl' : (l : ℕ) < n := by rw [← hi]; exact hl
      exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hl)))
        (ih l hl' l rfl (hy l))
  have heqZ : ∀ i, Submodule.span ℤ (b2 '' Set.Iio i) = Submodule.span ℤ (b1 '' Set.Iio i) :=
    fun i => le_antisymm (hle i) (hge i i rfl)
  have heqR : ∀ i, Submodule.span ℝ (b2 '' Set.Iio i) = Submodule.span ℝ (b1 '' Set.Iio i) := by
    intro i
    rw [← Submodule.span_span_of_tower ℤ ℝ (b2 '' Set.Iio i), heqZ i,
      Submodule.span_span_of_tower]
  have hproj : ∀ i, projOrth b2 i = projOrth b1 i := by
    intro i; unfold projOrth; simp only [heqR i]
  have hgs : ∀ i, gramSchmidt ℝ b2 i = gramSchmidt ℝ b1 i := by
    intro i
    rw [kz_gs_eq, kz_gs_eq, hproj i]
    have hyW : y i ∈ Submodule.span ℝ (b1 '' Set.Iio i) := by
      rw [← Submodule.span_span_of_tower ℤ ℝ (b1 '' Set.Iio i)]
      exact Submodule.subset_span (hy i)
    simp only [b2, map_sub, projOrth_eq_zero_of_mem b1 i hyW, sub_zero]
  have hgsN : ∀ i, gramSchmidtNormed ℝ b2 i = gramSchmidtNormed ℝ b1 i := by
    intro i; unfold gramSchmidtNormed; rw [hgs i]
  have hgsL : ∀ i, gsLen b2 i = gsLen b1 i := by intro i; unfold gsLen; rw [hgs i]
  have hlat : lattice b2 = lattice b1 := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨l, rfl⟩
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨l, rfl⟩) ?_
      exact Submodule.span_mono (Set.image_subset_range _ _) (hy l)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨l, rfl⟩
      have : b1 l = b2 l + y l := by simp [b2]
      rw [SetLike.mem_coe, this]
      refine Submodule.add_mem _ (Submodule.subset_span ⟨l, rfl⟩) ?_
      have hyl := hy l
      rw [← heqZ l] at hyl
      exact Submodule.span_mono (Set.image_subset_range _ _) hyl
  refine ⟨b2, kz_li_of_lattice b1 b2 hb1 hlat, hlat.trans hl1, ?_, ?_⟩
  · intro j
    rw [hgsL j]
    have hp : projLattice b2 j = projLattice b1 j := by
      unfold projLattice; rw [hproj j, hlat]
    rw [hp]; exact h1 j j.2
  · intro i j hji
    unfold gsCoeff
    rw [hgsN j, hgsL j, real_inner_comm]
    exact hyb i j hji


end KannanLattice.Core

open KannanLattice.Core


theorem solution (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ IsReduced b' := by
  exact kz_core m k b hb
