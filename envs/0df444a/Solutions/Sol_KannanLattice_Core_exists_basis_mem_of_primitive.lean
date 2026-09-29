-- Prove2me | solution 1 for KannanLattice.Core.exists_basis_mem_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:20:45.970816+00:00
-- url     : https://prove2.me/submissions/8b722a51-afc2-46e9-8bc0-11f4f0c53c33

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice



namespace KannanLattice.Core

open InnerProductSpace

lemma lattice_le_span {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    {v : EuclideanSpace ℝ (Fin k)} (hv : v ∈ lattice b) :
    v ∈ Submodule.span ℝ (Set.range b) := by
  unfold lattice at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ hx

theorem prim_core (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (v : EuclideanSpace ℝ (Fin k)) (hv : v ∈ lattice b) (hv0 : v ≠ 0)
    (hprim : ∀ t : ℝ, 0 < t → t < 1 → t • v ∉ lattice b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ v ∈ Set.range b' := by
  classical
  have hbZ : LinearIndependent ℤ b := hb.restrict_scalars' ℤ
  let b0 : Module.Basis (Fin m) ℤ (lattice b) := Module.Basis.span hbZ
  let v' : lattice b := ⟨v, hv⟩
  let N : Submodule ℤ (lattice b) := Submodule.span ℤ {v'}
  obtain ⟨n, S⟩ := Submodule.smithNormalForm b0 N
  have hv'N : v' ∈ N := Submodule.mem_span_singleton_self _
  have hn : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    have := S.bN.repr.injective (a₁ := ⟨v', hv'N⟩) (a₂ := 0) (Subsingleton.elim _ _)
    apply hv0
    have := congrArg (fun x : N => ((x : lattice b) : EuclideanSpace ℝ (Fin k))) this
    simpa [v'] using this
  let i0 : Fin n := ⟨0, hn⟩
  set e : lattice b := S.bM (S.f i0) with he
  have hsnf := S.snf i0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (S.bN i0).2
  have hne : (S.bN i0 : lattice b) ≠ 0 := by
    intro h; apply S.bN.ne_zero i0; exact Subtype.ext h
  have hE : c • v = S.a i0 • (e : EuclideanSpace ℝ (Fin k)) := by
    have := congrArg (fun x : lattice b => (x : EuclideanSpace ℝ (Fin k))) (hc.trans hsnf)
    simpa [v'] using this
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hne; rw [← hc, zero_smul]
  have ha0 : S.a i0 ≠ 0 := by
    intro h0; rw [h0, zero_smul, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_zero] at hE
    rcases hE with h | h
    · exact hc0 (by exact_mod_cast h)
    · exact hv0 h
  -- the real multiples of v in the lattice are integer multiples
  have hint : ∀ t : ℝ, t • v ∈ lattice b → ∃ q : ℤ, t = q := by
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
  let b' : Fin m → EuclideanSpace ℝ (Fin k) :=
    fun j => if j = S.f i0 then v else (S.bM j : EuclideanSpace ℝ (Fin k))
  have hb'mem : ∀ j, b' j ∈ lattice b := by
    intro j; simp only [b']; split_ifs
    · exact hv
    · exact (S.bM j).2
  have hbMmem : ∀ j, (S.bM j : EuclideanSpace ℝ (Fin k)) ∈ lattice b' := by
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
  have hlat : lattice b' = lattice b := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hb'mem j)
    · intro x hx
      have := S.bM.sum_repr ⟨x, hx⟩
      have hx' : x = ∑ j, S.bM.repr ⟨x, hx⟩ j • (S.bM j : EuclideanSpace ℝ (Fin k)) := by
        have h2 : ((∑ j, S.bM.repr ⟨x, hx⟩ j • S.bM j : lattice b) : EuclideanSpace ℝ (Fin k))
            = x := by rw [this]
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul_of_tower] at h2
        exact h2.symm
      rw [hx']
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbMmem j)
  have hspan : Submodule.span ℝ (Set.range b') = Submodule.span ℝ (Set.range b) := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact lattice_le_span b (hb'mem j))
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      apply lattice_le_span b'
      rw [hlat]
      exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨b', ?_, hlat, ⟨S.f i0, by simp [b']⟩⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  have := (linearIndependent_iff_card_eq_finrank_span.1 hb)
  rw [this]
  unfold Set.finrank
  rw [hspan]

end KannanLattice.Core

open KannanLattice.Core


theorem solution (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (v : EuclideanSpace ℝ (Fin k)) (hv : v ∈ lattice b) (hv0 : v ≠ 0)
    (hprim : ∀ t : ℝ, 0 < t → t < 1 → t • v ∉ lattice b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ v ∈ Set.range b' := by
  exact prim_core m k b hb v hv hv0 hprim
