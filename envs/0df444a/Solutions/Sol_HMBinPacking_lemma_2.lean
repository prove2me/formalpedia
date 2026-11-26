-- Prove2me | solution 1 for HMBinPacking.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:05:10.615603+00:00
-- url     : https://prove2.me/submissions/3a7aa0c2-2bc2-417c-920d-d774c9593d77

import Mathlib
import Definitions.Def_HMBinPacking_LatticePolytope
import Theorems.Thm_HMBinPacking_lemma_3

open scoped Pointwise
open HMBinPacking
open Finset

private theorem distribute {ι : Type*} [Fintype ι] (u : ι → ℕ) (k : ℕ)
    (hk : k ≤ ∑ i, u i) : ∃ b : ι → ℕ, (∀ i, b i ≤ u i) ∧ ∑ i, b i = k := by
  classical
  induction k with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨b, hb, hsum⟩ := ih (by omega)
    obtain ⟨j, hj⟩ : ∃ j, b j < u j := by
      by_contra! h
      have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
      omega
    refine ⟨fun i => b i + if i = j then 1 else 0, ?_, ?_⟩
    · intro i
      by_cases e : i = j
      · subst i; simp; omega
      · simpa [e] using hb i
    · simp [Finset.sum_add_distrib, hsum]

private theorem combo {d m : ℕ} (V : Set (Fin d → ℤ)) (v : Fin m → Fin d → ℤ)
    (hv : ∀ i, v i ∈ V) (α : Fin m → ℝ) (ha : ∀ i, 0 ≤ α i)
    (k : ℝ) (hk : 0 < k) (hsum : ∑ i, α i = k) :
    (∑ i, α i • zCast (v i)) ∈ k • convexHull ℝ (zCast '' V) := by
  refine ⟨∑ i, (α i / k) • zCast (v i), ?_, ?_⟩
  · apply (convex_convexHull ℝ _).sum_mem
    · intro i _; exact div_nonneg (ha i) hk.le
    · rw [← Finset.sum_div, hsum, div_self hk.ne']
    · intro i _; exact subset_convexHull ℝ _ ⟨_, hv i, rfl⟩
  · change k • (∑ i, (α i / k) • zCast (v i)) = _
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [smul_smul, mul_div_cancel₀ _ hk.ne']

private theorem cast_sum {d m : ℕ} (b : Fin m → ℕ) (v : Fin m → Fin d → ℤ) :
    zCast (∑ i, b i • v i) = ∑ i, (b i : ℝ) • zCast (v i) := by
  ext j
  simp [zCast, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul]

private theorem split_weights {d k : ℕ} (hdk : d ≤ k) (hk : 0 < k)
    (V : Set (Fin d → ℤ)) (v : Fin (d+1) → Fin d → ℤ) (hv : ∀ i, v i ∈ V)
    (r : Fin d → ℤ) (n : ℕ) (hn : 0 < n) (z : Fin d → ℤ)
    (α : Fin (d+1) → ℝ) (ha : ∀ i, 0 ≤ α i)
    (hsum : ∑ i, α i = (n : ℝ) * k)
    (he : zCast z = (n : ℝ) • zCast r + ∑ i, α i • zCast (v i)) :
    ∃ p : Fin n → Fin d → ℤ,
      (∀ j, zCast (p j) ∈ (fun x => zCast r + x) '' ((k : ℝ) • convexHull ℝ (zCast '' V))) ∧
      ∑ j, p j = z := by
  classical
  induction n generalizing z α with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨fun _ => z, fun _ => ⟨_, combo V v hv α ha k (by exact_mod_cast hk)
        (by simpa using hsum), by simpa using he.symm⟩, by simp⟩
    let u := fun i => ⌊α i⌋₊
    have hlt : ∑ i, α i < ∑ i, ((u i : ℝ) + 1) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => Nat.lt_floor_add_one _
    have hnlt : (n+1)*k < (∑ i, u i) + (d+1) := by
      rw [hsum, Finset.sum_add_distrib] at hlt
      have h : ((n+1 : ℕ) : ℝ) * (k : ℝ) < (((∑ i, u i) + (d+1) : ℕ) : ℝ) := by
        simpa using hlt
      exact_mod_cast h
    have hfloor : k ≤ ∑ i, u i := by nlinarith [Nat.le_mul_of_pos_left k (by omega : 0<n)]
    obtain ⟨b, hb, hbs⟩ := distribute u k hfloor
    have hb' (i) : (b i : ℝ) ≤ α i :=
      le_trans (by exact_mod_cast hb i) (Nat.floor_le (ha i))
    let y := r + ∑ i, b i • v i
    have hy : zCast y = zCast r + ∑ i, (b i : ℝ) • zCast (v i) := by
      rw [← cast_sum]; ext j; simp [y,zCast]
    have hmem : zCast y ∈ (fun x => zCast r + x) '' ((k : ℝ) • convexHull ℝ (zCast '' V)) :=
      ⟨_,combo V v hv (fun i => (b i : ℝ)) (fun _ => by positivity) k
        (by exact_mod_cast hk) (by exact_mod_cast hbs),hy.symm⟩
    have hx : zCast (z-y) = (n : ℝ) • zCast r +
        ∑ i, (α i - (b i : ℝ)) • zCast (v i) := by
      have hsub : zCast (z-y) = zCast z - zCast y := by ext j; simp [zCast]
      rw [hsub, he, hy]
      simp_rw [sub_smul]; rw [Finset.sum_sub_distrib, Nat.cast_succ, add_smul, one_smul]; abel
    obtain ⟨p, hp, hpz⟩ := ih (by omega) (z-y) (fun i => α i - b i)
      (fun i => sub_nonneg.mpr (hb' i)) (by
        rw [Finset.sum_sub_distrib, hsum]; have hbr : ∑ i, (b i : ℝ) = (k : ℝ) := by exact_mod_cast hbs
        rw [hbr, Nat.cast_succ]; ring) hx
    refine ⟨Fin.cons y p, ?_, ?_⟩
    · exact Fin.cases hmem hp
    · rw [Fin.sum_univ_succ]; simp [hpz]

private theorem translated_lattice {d : ℕ} (V : Set (Fin d → ℤ)) (hf : V.Finite)
    (hne : V.Nonempty) (k : ℤ) (r : Fin d → ℤ) :
    IsLatticePolytope ((fun x => zCast r + x) '' ((k : ℝ) • convexHull ℝ (zCast '' V))) := by
  let f := fun v : Fin d → ℤ => r + k • v
  refine ⟨f '' V, hf.image _, hne.image _, ?_⟩
  rw [← convexHull_smul]
  change zCast r +ᵥ convexHull ℝ ((k : ℝ) • (zCast '' V)) = _
  rw [← convexHull_vadd]
  congr 1
  ext x
  have hcast (v : Fin d → ℤ) : zCast (f v) = zCast r + (k : ℝ) • zCast v := by
    ext j; simp [f,zCast,Pi.smul_apply,zsmul_eq_mul]
  constructor
  · rintro ⟨_, ⟨_, ⟨v,hv,rfl⟩,rfl⟩,rfl⟩
    exact ⟨_, ⟨v,hv,rfl⟩, hcast v⟩
  · rintro ⟨_, ⟨v,hv,rfl⟩,rfl⟩
    exact ⟨_, ⟨_, ⟨v,hv,rfl⟩,rfl⟩, (hcast v).symm⟩

theorem solution {d : ℕ} (V : Set (Fin d → ℤ)) (hVfin : V.Finite) (hVne : V.Nonempty) (k : ℤ)
    (hk : (d : ℤ) ≤ k) (r : Fin d → ℤ) :
    HasIDP ((fun x => zCast r + x) '' ((k : ℝ) • convexHull ℝ (zCast '' V))) := by
  classical
  refine ⟨translated_lattice V hVfin hVne k r, ?_⟩
  intro n hn z hz
  obtain ⟨_,⟨_,⟨x,hx,rfl⟩,rfl⟩,he⟩ := hz
  by_cases hd : d = 0
  · subst d
    refine ⟨fun _ => z, fun _ => ⟨_, ⟨x,hx,rfl⟩, Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩
  lift k to ℕ using (by omega : 0 ≤ k)
  have hdk : d ≤ k := by exact_mod_cast hk
  have hkpos : 0 < k := by omega
  push_cast at he ⊢
  have ht : (0:ℝ) < n * k := by positivity
  obtain ⟨v,α,hv,ha,hz,hα⟩ := lemma_3 (zCast '' V) (hVfin.image _) (hVne.image _)
    ((n : ℝ)*k) ht (((n : ℝ)*k) • x) ⟨x,hx,rfl⟩
  choose w hw hwe using hv
  have e : zCast z = (n : ℝ) • zCast r + ∑ i, α i • zCast (w i) := by
    rw [← he, smul_add, smul_smul,hz]; simp only [hwe]
  exact split_weights hdk hkpos V w hw r n (by omega) z α ha hα e
