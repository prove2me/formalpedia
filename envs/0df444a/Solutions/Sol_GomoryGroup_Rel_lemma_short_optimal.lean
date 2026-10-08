-- Prove2me | solution 1 for GomoryGroup.Rel.lemma_short_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:26:52.502119+00:00
-- url     : https://prove2.me/submissions/4395ad85-36b8-448e-ae28-a841ab879858

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting



namespace GomoryGroup.Rel

open Matrix

theorem zero_sum_list {G : Type*} [AddCommGroup G] [Fintype G] (l : List G)
    (h : Fintype.card G ≤ l.length) :
    ∃ i j, i < j ∧ j ≤ l.length ∧ ((l.take j).drop i).sum = 0 := by
  let f : Fin (Fintype.card G + 1) → G := fun k => (l.take k).sum
  have hlt : Fintype.card G < Fintype.card (Fin (Fintype.card G + 1)) := by simp
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  have key : ∀ a b : ℕ, a < b → b ≤ l.length → (l.take a).sum = (l.take b).sum →
      ∃ i j, i < j ∧ j ≤ l.length ∧ ((l.take j).drop i).sum = 0 := by
    intro a b hab hb hs
    refine ⟨a, b, hab, hb, ?_⟩
    have h1 : l.take b = (l.take b).take a ++ (l.take b).drop a := (List.take_append_drop a _).symm
    have h2 : (l.take b).take a = l.take a := by
      rw [List.take_take]; congr 1; omega
    rw [h1, h2, List.sum_append] at hs
    simpa using hs
  have hb : ∀ k : Fin (Fintype.card G + 1), (k : ℕ) ≤ l.length := fun k => by
    have := k.2; omega
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt' | hlt'
  · exact key _ _ hlt' (hb _) hfab
  · exact key _ _ hlt' (hb _) hfab.symm


theorem card_core {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hB : B.det ≠ 0) :
    Finite ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) ∧
      Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detD B := by
  have hinj : Function.Injective (Matrix.mulVecLin B) := by
    intro x y hxy
    have : B.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hB this
    exact sub_eq_zero.mp h2
  let e : (Fin m → ℤ) ≃ₗ[ℤ] LinearMap.range (Matrix.mulVecLin B) :=
    LinearEquiv.ofInjective (Matrix.mulVecLin B) hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.mulVecLin B)) e
  have hcomp : (LinearMap.range (Matrix.mulVecLin B)).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((e : (Fin m → ℤ) →+ _)) = Matrix.mulVecLin B := by
    ext x : 1
    rfl
  have hd : LinearMap.det (Matrix.mulVecLin B) = B.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  have hcard : Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detD B := by
    rw [← h]
    unfold detD
    rw [hcomp, hd]
  refine ⟨?_, hcard⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  unfold detD
  exact Int.natAbs_ne_zero.mpr hB


def cnt {n : ℕ} (M : List (Fin n)) : Fin n → ℕ := fun j => M.count j

theorem mk_cnt {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (M : List (Fin n)) :
    (Submodule.Quotient.mk (p := LinearMap.range (Matrix.mulVecLin B))
        (N *ᵥ (fun j => ((cnt M j : ℕ) : ℤ)))) =
      (M.map (fun a => (Submodule.Quotient.mk (p := LinearMap.range (Matrix.mulVecLin B))
        (fun r => N r a)))).sum := by
  induction M with
  | nil =>
    simp [cnt]
    exact ⟨0, by ext r; simp [Matrix.mulVec, dotProduct]⟩
  | cons a M ih =>
    have hc : (fun j => ((cnt (a :: M) j : ℕ) : ℤ)) =
        (fun j => ((cnt M j : ℕ) : ℤ)) + Pi.single a 1 := by
      ext j
      by_cases h : a = j <;> simp [cnt, List.count_cons, Pi.single_apply, h]
    have hcol : N *ᵥ (Pi.single a 1 : Fin n → ℤ) = fun r => N r a := by
      ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hc, Matrix.mulVec_add, hcol, Submodule.Quotient.mk_add, ih, List.map_cons, List.sum_cons]
    abel

theorem list_of_counts {n : ℕ} (y : Fin n → ℕ) :
    ∃ L : List (Fin n), (∀ j, L.count j = y j) ∧ L.length = ∑ j, y j := by
  refine ⟨(List.finRange n).flatMap (fun j => List.replicate (y j) j), ?_, ?_⟩
  · intro j
    simp [List.count_flatMap, List.count_replicate, ← Fin.sum_univ_def]
  · simp [List.length_flatMap, ← Fin.sum_univ_def]

theorem reduce_step {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0)
    (hopt : ∀ j, reducedCost B N cB cN j ≤ 0) (y : Fin n → ℕ)
    (hfeas : IsGroupFeasible B N b y) (hD : detD B ≤ ∑ j, y j) :
    ∃ y' : Fin n → ℕ, IsGroupFeasible B N b y' ∧ ∑ j, y' j < ∑ j, y j ∧
      groupObj B N cB cN y ≤ groupObj B N cB cN y' := by
  obtain ⟨hfin, hcard⟩ := card_core B hB
  letI : Fintype ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) := Fintype.ofFinite _
  have hc : Fintype.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detD B := by
    rw [← hcard, Nat.card_eq_fintype_card]
  obtain ⟨L, hLc, hLl⟩ := list_of_counts y
  let g : Fin n → ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) :=
    fun a => Submodule.Quotient.mk (fun r => N r a)
  obtain ⟨i, j, hij, hjl, hsum⟩ := zero_sum_list (L.map g)
    (by rw [List.length_map, hLl, hc]; exact hD)
  set M : List (Fin n) := (L.take j).drop i with hMdef
  have hM : (M.map g).sum = 0 := by
    rw [hMdef, List.map_drop, List.map_take]; exact hsum
  have hz : N *ᵥ (fun a => ((cnt M a : ℕ) : ℤ)) ∈ LinearMap.range (Matrix.mulVecLin B) := by
    rw [← Submodule.Quotient.mk_eq_zero, mk_cnt]
    exact hM
  obtain ⟨k0, hk0⟩ := hz
  have hk0' : B *ᵥ k0 = N *ᵥ (fun a => ((cnt M a : ℕ) : ℤ)) := hk0
  have hsub : M.Sublist L := (List.drop_sublist _ _).trans (List.take_sublist _ _)
  have hle : ∀ a, cnt M a ≤ y a := fun a => (hsub.count_le a).trans (hLc a).le
  have hjl' : j ≤ L.length := by simpa using hjl
  have hMlen : M.length = j - i := by
    simp only [hMdef, List.length_drop, List.length_take]
    congr 1
    omega
  have hMne : M ≠ [] := by
    intro h
    rw [h] at hMlen
    simp at hMlen
    omega
  obtain ⟨a0, ha0⟩ := List.exists_mem_of_ne_nil _ hMne
  have hcnt0 : 0 < cnt M a0 := List.count_pos_iff.mpr ha0
  let y' : Fin n → ℕ := fun a => y a - cnt M a
  have hyz : ∀ a, y' a + cnt M a = y a := fun a => Nat.sub_add_cancel (hle a)
  have hsumyz : ∑ a, y' a + ∑ a, cnt M a = ∑ a, y a := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => hyz a)
  have hpos : 0 < ∑ a, cnt M a :=
    lt_of_lt_of_le hcnt0 (Finset.single_le_sum (f := fun a => cnt M a) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a0))
  refine ⟨y', ?_, by omega, ?_⟩
  · obtain ⟨k, hk⟩ := hfeas
    refine ⟨k + k0, ?_⟩
    have hcast : (fun a => ((y a : ℕ) : ℤ)) =
        (fun a => ((y' a : ℕ) : ℤ)) + (fun a => ((cnt M a : ℕ) : ℤ)) := by
      ext a
      have := hyz a
      simp only [Pi.add_apply]
      exact_mod_cast this.symm
    rw [Matrix.mulVec_add, hk0', ← hk, hcast, Matrix.mulVec_add]
    abel
  · have h1 : groupObj B N cB cN y =
        groupObj B N cB cN y' + groupObj B N cB cN (cnt M) := by
      unfold groupObj
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← mul_add, ← Nat.cast_add, hyz a]
    have h2 : groupObj B N cB cN (cnt M) ≤ 0 := by
      unfold groupObj
      apply Finset.sum_nonpos
      intro a _
      exact mul_nonpos_of_nonpos_of_nonneg (hopt a) (Nat.cast_nonneg _)
    linarith

theorem reduce_all {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0)
    (hopt : ∀ j, reducedCost B N cB cN j ≤ 0) :
    ∀ s : ℕ, ∀ y : Fin n → ℕ, ∑ j, y j = s → IsGroupFeasible B N b y →
      ∃ y' : Fin n → ℕ, IsGroupFeasible B N b y' ∧ ∑ j, y' j ≤ detD B - 1 ∧
        groupObj B N cB cN y ≤ groupObj B N cB cN y' := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro y hs hfeas
    have hD : 1 ≤ detD B := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hB)
    by_cases hsmall : ∑ j, y j ≤ detD B - 1
    · exact ⟨y, hfeas, hsmall, le_rfl⟩
    · obtain ⟨y', hf', hlt, hobj⟩ := reduce_step B N cB cN b hB hopt y hfeas (by omega)
      obtain ⟨y'', hf'', hs'', hobj''⟩ := ih _ (hs ▸ hlt) y' rfl hf'
      exact ⟨y'', hf'', hs'', hobj.trans hobj''⟩

theorem feasible_exists {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hB : B.det ≠ 0) (hI : HasUnitColumns B N) :
    ∃ y : Fin n → ℕ, IsGroupFeasible B N b y := by
  obtain ⟨hfin, hcard⟩ := card_core B hB
  have hD : 1 ≤ detD B := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hB)
  obtain ⟨d, hd⟩ : ∃ d, detD B = d + 1 := ⟨detD B - 1, by omega⟩
  -- the monoid of reachable right-hand sides is a subgroup
  have hdel : ∀ x : Fin m → ℤ, (d + 1) • x ∈ LinearMap.range (Matrix.mulVecLin B) := by
    intro x
    have h0 : (Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B))) •
        (Submodule.Quotient.mk x :
          (Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = 0 := by
      haveI := hfin
      exact card_nsmul_eq_zero'
    rw [hcard, hd, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  let T : AddSubgroup (Fin m → ℤ) :=
    { carrier := {x | ∃ (y : Fin n → ℕ) (k : Fin m → ℤ),
        x = N *ᵥ (fun j => ((y j : ℕ) : ℤ)) + B *ᵥ k}
      zero_mem' := ⟨0, 0, by ext r; simp [Matrix.mulVec, dotProduct]⟩
      add_mem' := by
        rintro _ _ ⟨y1, k1, rfl⟩ ⟨y2, k2, rfl⟩
        refine ⟨y1 + y2, k1 + k2, ?_⟩
        have : (fun j => (((y1 + y2) j : ℕ) : ℤ)) =
            (fun j => ((y1 j : ℕ) : ℤ)) + (fun j => ((y2 j : ℕ) : ℤ)) := by
          ext j; simp
        rw [this, Matrix.mulVec_add, Matrix.mulVec_add]; abel
      neg_mem' := by
        rintro x ⟨y, k, rfl⟩
        obtain ⟨k1, hk1⟩ := hdel (N *ᵥ (fun j => ((y j : ℕ) : ℤ)) + B *ᵥ k)
        have hk1' : B *ᵥ k1 = (d + 1) • (N *ᵥ (fun j => ((y j : ℕ) : ℤ)) + B *ᵥ k) := hk1
        refine ⟨d • y, d • k - k1, ?_⟩
        have hcast : (fun j => (((d • y) j : ℕ) : ℤ)) = d • (fun j => ((y j : ℕ) : ℤ)) := by
          ext j; simp
        rw [hcast, Matrix.mulVec_sub, hk1', Matrix.mulVec_smul, Matrix.mulVec_smul, succ_nsmul]
        rw [smul_add]
        abel }
  have hmem : ∀ i : Fin m, (Pi.single i 1 : Fin m → ℤ) ∈ T := by
    intro i
    rcases hI i with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨0, Pi.single j 1, ?_⟩
      have hcol : B *ᵥ (Pi.single j 1 : Fin m → ℤ) = Pi.single i 1 := by
        ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply, hj r]
      rw [hcol]; ext r; simp [Matrix.mulVec, dotProduct]
    · refine ⟨Pi.single j 1, 0, ?_⟩
      have hcol : N *ᵥ (fun a => (((Pi.single j 1 : Fin n → ℕ) a : ℕ) : ℤ)) = Pi.single i 1 := by
        ext r
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, hj r]
      rw [hcol]; ext r; simp [Matrix.mulVec, dotProduct]
  have hb : b ∈ T := by
    have : b = ∑ i, b i • (Pi.single i 1 : Fin m → ℤ) := by
      ext r; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact AddSubgroup.sum_mem _ (fun i _ => AddSubgroup.zsmul_mem _ (hmem i) _)
  obtain ⟨y, k, hyk⟩ := hb
  exact ⟨y, k, by rw [hyk]; abel⟩

theorem short_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N) (hopt : ∀ j, reducedCost B N cB cN j ≤ 0) :
    ∃ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1 := by
  obtain ⟨y0, hy0⟩ := feasible_exists B N b hB hI
  obtain ⟨y1, hf1, hs1, -⟩ := reduce_all B N cB cN b hB hopt _ y0 rfl hy0
  let S : Set (Fin n → ℕ) := {y | IsGroupFeasible B N b y ∧ ∑ j, y j ≤ detD B - 1}
  have hfin : S.Finite := by
    apply (Set.finite_Iic (fun _ : Fin n => detD B - 1)).subset
    intro y hy j
    have : y j ≤ ∑ j, y j := Finset.single_le_sum (f := fun j => y j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    exact this.trans hy.2
  obtain ⟨y, hyS, hymax⟩ := Set.exists_max_image S (groupObj B N cB cN) hfin ⟨y1, hf1, hs1⟩
  refine ⟨y, ⟨hyS.1, ?_⟩, hyS.2⟩
  intro y' hy'
  obtain ⟨y'', hf'', hs'', hobj⟩ := reduce_all B N cB cN b hB hopt _ y' rfl hy'
  exact hobj.trans (hymax y'' ⟨hf'', hs''⟩)

end GomoryGroup.Rel

open GomoryGroup.Rel
open Matrix

theorem solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N) (hopt : ∀ j, reducedCost B N cB cN j ≤ 0) :
    ∃ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1 := by
  exact short_core B N cB cN b hB hI hopt
