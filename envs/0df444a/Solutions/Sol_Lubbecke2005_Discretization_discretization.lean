-- Prove2me | solution 1 for Lubbecke2005.Discretization.discretization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:27:39.728346+00:00
-- url     : https://prove2.me/submissions/c3883cd2-8ccb-4ad7-9727-1708c635cd2e

import Mathlib
import Definitions.Def_Lubbecke2005_Discretization_Polyhedron



namespace Lubbecke2005.Discretization

/-- minimal elements of `S` w.r.t. the key `K`. -/
def minSet {α ι : Type} (K : α → ι → ℕ) (S : Set α) : Set α :=
  {u | u ∈ S ∧ ∀ v ∈ S, K v ≤ K u → v = u}

lemma minSet_finite {α ι : Type} [Finite ι] (K : α → ι → ℕ) (S : Set α)
    (hK : Set.InjOn K S) : (minSet K S).Finite := by
  apply Set.Finite.of_finite_image _ (hK.mono (fun u hu => hu.1))
  apply WellQuasiOrderedLE.finite_of_isAntichain
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne hle
  exact hne (by rw [hv.2 u hu.1 hle])

lemma minSet_below {α ι : Type} [Fintype ι] (K : α → ι → ℕ) (S : Set α)
    (hK : Set.InjOn K S) : ∀ z ∈ S, ∃ u ∈ minSet K S, K u ≤ K z := by
  suffices h : ∀ N, ∀ z ∈ S, ∑ i, K z i = N → ∃ u ∈ minSet K S, K u ≤ K z by
    intro z hz; exact h _ z hz rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z hz hN
    by_cases hmin : ∀ v ∈ S, K v ≤ K z → v = z
    · exact ⟨z, ⟨hz, hmin⟩, le_rfl⟩
    push Not at hmin
    obtain ⟨v, hv, hle, hne⟩ := hmin
    have hKne : K v ≠ K z := fun h => hne (hK hv hz h)
    have hlt : ∑ i, K v i < ∑ i, K z i := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hKne
      exact Finset.sum_lt_sum (fun i _ => hle i) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hle i) hi⟩
    obtain ⟨u, hu, hle'⟩ := ih _ (hN ▸ hlt) v hv rfl
    exact ⟨u, hu, hle'.trans hle⟩

lemma exists_scale {ι : Type} [Fintype ι] (f : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ z : ℤ, (z : ℚ) = N * f i := by
  refine ⟨∏ i, (f i).den, Finset.prod_pos (fun i _ => (f i).den_pos), fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun i => (f i).den) (Finset.mem_univ i)
  refine ⟨(f i).num * c, ?_⟩
  rw [hc]
  push_cast
  rw [← Rat.mul_den_eq_num (f i)]
  ring

/-- integer polyhedron with data `A`, `b`. -/
def XS {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : Set (Fin n → ℤ) :=
  {z | (∀ j, 0 ≤ z j) ∧ ∀ i, b i ≤ ∑ j, A i j * z j}

def keyv {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (z : Fin n → ℤ) :
    Fin n ⊕ Fin m → ℕ :=
  Sum.elim (fun j => (z j).toNat) (fun i => (∑ j, A i j * z j - b i).toNat)

lemma keyv_inj {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (S : Set (Fin n → ℤ))
    (hS : S ⊆ XS A b) : Set.InjOn (keyv A b) S := by
  intro z hz z' hz' h
  funext j
  have h1 := congrFun h (Sum.inl j)
  have h2 := (hS hz).1 j
  have h3 := (hS hz').1 j
  simp only [keyv, Sum.elim_inl] at h1
  omega

lemma keyv_sub {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (z z' : Fin n → ℤ)
    (hz : z ∈ XS A b) (hz' : z' ∈ XS A b) (hle : keyv A b z ≤ keyv A b z') :
    z' - z ∈ XS A 0 := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · have h1 := hle (Sum.inl j)
    have h2 := hz.1 j
    have h3 := hz'.1 j
    simp only [keyv, Sum.elim_inl] at h1
    simp only [Pi.sub_apply]
    omega
  · have h1 := hle (Sum.inr i)
    have h2 := hz.2 i
    have h3 := hz'.2 i
    simp only [keyv, Sum.elim_inr] at h1
    have e : ∑ j, A i j * (z' - z) j = ∑ j, A i j * z' j - ∑ j, A i j * z j := by
      simp [mul_sub, Finset.sum_sub_distrib]
    simp only [Pi.zero_apply]
    rw [e]
    omega

/-- Hilbert basis representation. -/
lemma hilbert_rep {m n : ℕ} (A : Fin m → Fin n → ℤ) :
    ∃ H : Finset (Fin n → ℤ), (∀ u ∈ H, u ∈ XS A 0 ∧ u ≠ 0) ∧
      ∀ w ∈ XS A 0, ∃ c : (Fin n → ℤ) → ℕ, w = ∑ u ∈ H, c u • u := by
  classical
  set S0 : Set (Fin n → ℤ) := XS A 0 \ {0} with hS0
  have hsub : S0 ⊆ XS A 0 := Set.sdiff_subset
  have hinj := keyv_inj A 0 S0 hsub
  have hfin := minSet_finite (keyv A 0) S0 hinj
  refine ⟨hfin.toFinset, fun u hu => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hu
    exact ⟨hsub hu.1, fun h => hu.1.2 h⟩
  suffices h : ∀ N, ∀ w ∈ XS A 0, ∑ j, (w j).toNat = N →
      ∃ c : (Fin n → ℤ) → ℕ, w = ∑ u ∈ hfin.toFinset, c u • u by
    intro w hw; exact h _ w hw rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hN
    by_cases hw0 : w = 0
    · exact ⟨0, by simp [hw0]⟩
    have hwS : w ∈ S0 := ⟨hw, hw0⟩
    obtain ⟨u, hu, hle⟩ := minSet_below (keyv A 0) S0 hinj w hwS
    have hd := keyv_sub A 0 u w (hsub hu.1) hw hle
    have hu0 : u ≠ 0 := hu.1.2
    have hlt : ∑ j, ((w - u) j).toNat < ∑ j, (w j).toNat := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hu0
      apply Finset.sum_lt_sum
      · intro i _
        have := (hsub hu.1).1 i
        simp only [Pi.sub_apply]
        omega
      · refine ⟨j, Finset.mem_univ _, ?_⟩
        have h1 := (hsub hu.1).1 j
        have h2 := hd.1 j
        simp only [Pi.sub_apply, Pi.zero_apply] at hj h2 ⊢
        omega
    obtain ⟨c, hc⟩ := ih _ (hN ▸ hlt) (w - u) hd rfl
    refine ⟨fun v => c v + if v = u then 1 else 0, ?_⟩
    have huF : u ∈ hfin.toFinset := (Set.Finite.mem_toFinset _).2 hu
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', huF, if_true]
    rw [← hc]
    abel


lemma castVec_lin {n k l : ℕ} (a : Fin k → ℕ) (p : Fin k → Fin n → ℤ) (c : Fin l → ℕ)
    (w : Fin l → Fin n → ℤ) :
    castVec (∑ q, a q • p q + ∑ r, c r • w r) =
      ∑ q, (a q : ℝ) • castVec (p q) + ∑ r, (c r : ℝ) • castVec (w r) := by
  funext j
  simp [castVec, Finset.sum_apply]

theorem discretization_core {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ) :
    ∃ (k l : ℕ) (p : Fin k → (Fin n → ℤ)) (w : Fin l → (Fin n → ℤ)),
      (∀ q, castVec (p q) ∈ integerPoints D d) ∧
      (∀ r, IsIntegerRay D (w r)) ∧
      integerPoints D d =
        {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧
          ∃ (lamQ : Fin k → ℕ) (lamR : Fin l → ℕ),
            ∑ q, lamQ q = 1 ∧
            x = ∑ q, (lamQ q : ℝ) • castVec (p q) + ∑ r, (lamR r : ℝ) • castVec (w r)} := by
  classical
  obtain ⟨N, hN, hz⟩ := exists_scale (Sum.elim (fun p : Fin m × Fin n => D p.1 p.2) d)
  choose g hg using hz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨A, hA⟩ : ∃ A : Fin m → Fin n → ℤ, ∀ i j, (A i j : ℝ) = N * (D i j : ℝ) := by
    refine ⟨fun i j => g (Sum.inl (i, j)), fun i j => ?_⟩
    have h1 := hg (Sum.inl (i, j))
    simp only [Sum.elim_inl] at h1
    have h2 : (((g (Sum.inl (i, j)) : ℚ)) : ℝ) = (((N : ℚ) * D i j : ℚ) : ℝ) := by rw [h1]
    push_cast at h2
    exact h2
  obtain ⟨b, hb⟩ : ∃ b : Fin m → ℤ, ∀ i, (b i : ℝ) = N * (d i : ℝ) := by
    refine ⟨fun i => g (Sum.inr i), fun i => ?_⟩
    have h1 := hg (Sum.inr i)
    simp only [Sum.elim_inr] at h1
    have h2 : (((g (Sum.inr i) : ℚ)) : ℝ) = (((N : ℚ) * d i : ℚ) : ℝ) := by rw [h1]
    push_cast at h2
    exact h2
  have hsum : ∀ (z : Fin n → ℤ) i,
      ((∑ j, A i j * z j : ℤ) : ℝ) = N * ∑ j, (D i j : ℝ) * castVec z j := by
    intro z i
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hA]; simp [castVec]; ring
  have hpoly : ∀ z : Fin n → ℤ, castVec z ∈ polyhedronP D d ↔ z ∈ XS A b := by
    intro z
    simp only [polyhedronP, XS, Set.mem_setOf_eq]
    have hj : ∀ j, (0 ≤ castVec z j ↔ 0 ≤ z j) := fun j => by simp [castVec]
    have hi : ∀ i, ((d i : ℝ) ≤ ∑ j, (D i j : ℝ) * castVec z j ↔ b i ≤ ∑ j, A i j * z j) := by
      intro i
      rw [← Int.cast_le (R := ℝ), hsum, hb]
      exact (mul_le_mul_iff_of_pos_left hNpos).symm
    simp only [hj, hi]
    tauto
  have hrec : ∀ z : Fin n → ℤ, castVec z ∈ recessionConeP D ↔ z ∈ XS A 0 := by
    intro z
    simp only [recessionConeP, XS, Set.mem_setOf_eq]
    have hj : ∀ j, (0 ≤ castVec z j ↔ 0 ≤ z j) := fun j => by simp [castVec]
    have hi : ∀ i, ((0 : ℝ) ≤ ∑ j, (D i j : ℝ) * castVec z j ↔ (0 : Fin m → ℤ) i ≤ ∑ j, A i j * z j) := by
      intro i
      rw [Pi.zero_apply, ← Int.cast_le (R := ℝ), hsum, Int.cast_zero]
      constructor
      · intro h; positivity
      · intro h; exact nonneg_of_mul_nonneg_right (by linarith) hNpos
    simp only [hj, hi]
    tauto
  -- generating points
  have hinjX := keyv_inj A b (XS A b) le_rfl
  have hfinX := minSet_finite (keyv A b) (XS A b) hinjX
  obtain ⟨H, hH, hrep⟩ := hilbert_rep A
  set F := hfinX.toFinset with hF
  refine ⟨F.card, H.card, fun q => (F.equivFin.symm q).1, fun r => (H.equivFin.symm r).1,
    ?_, ?_, ?_⟩
  · intro q
    have hq : (F.equivFin.symm q).1 ∈ minSet (keyv A b) (XS A b) :=
      (Set.Finite.mem_toFinset _).1 (F.equivFin.symm q).2
    exact ⟨(hpoly _).2 hq.1, _, rfl⟩
  · intro r
    have hr := hH _ (H.equivFin.symm r).2
    refine ⟨fun h => hr.2 h, (hrec _).2 hr.1⟩
  ext x
  constructor
  · rintro ⟨hx, z, rfl⟩
    refine ⟨hx.2, ?_⟩
    have hzX := (hpoly z).1 hx
    obtain ⟨u, hu, hle⟩ := minSet_below (keyv A b) (XS A b) hinjX z hzX
    have hd := keyv_sub A b u z hu.1 hzX hle
    obtain ⟨c, hc⟩ := hrep _ hd
    have huF : u ∈ F := (Set.Finite.mem_toFinset _).2 hu
    set q0 := F.equivFin ⟨u, huF⟩ with hq0
    refine ⟨fun q => if q = q0 then 1 else 0, fun r => c (H.equivFin.symm r).1, by simp, ?_⟩
    rw [← castVec_lin]
    congr 1
    have e1 : ∑ q, (if q = q0 then 1 else 0) • (F.equivFin.symm q).1 = u := by
      simp [hq0]
    have e2 : ∑ r, c (H.equivFin.symm r).1 • (H.equivFin.symm r).1 = ∑ v ∈ H, c v • v := by
      rw [← Finset.sum_coe_sort H]
      exact Equiv.sum_comp H.equivFin.symm (fun v : H => c v.1 • v.1)
    rw [e1, e2, ← hc]
    abel
  · rintro ⟨-, lamQ, lamR, h1, rfl⟩
    rw [← castVec_lin]
    refine ⟨(hpoly _).2 ?_, _, rfl⟩
    set p := fun q => (F.equivFin.symm q).1 with hp
    set w := fun r => (H.equivFin.symm r).1 with hw
    have hpX : ∀ q, p q ∈ XS A b := by
      intro q
      have hq : (F.equivFin.symm q).1 ∈ minSet (keyv A b) (XS A b) :=
        (Set.Finite.mem_toFinset _).1 (F.equivFin.symm q).2
      exact hq.1
    have hwX : ∀ r, w r ∈ XS A 0 := fun r => (hH _ (H.equivFin.symm r).2).1
    have hap : ∀ j, (∑ q, lamQ q • p q + ∑ r, lamR r • w r) j =
        ∑ q, (lamQ q : ℤ) * p q j + ∑ r, (lamR r : ℤ) * w r j := by
      intro j; simp [Finset.sum_apply]
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [hap]
      exact add_nonneg (Finset.sum_nonneg (fun q _ => mul_nonneg (by positivity) ((hpX q).1 j)))
        (Finset.sum_nonneg (fun r _ => mul_nonneg (by positivity) ((hwX r).1 j)))
    · have e : ∑ j, A i j * (∑ q, lamQ q • p q + ∑ r, lamR r • w r) j =
          ∑ q, (lamQ q : ℤ) * ∑ j, A i j * p q j + ∑ r, (lamR r : ℤ) * ∑ j, A i j * w r j := by
        rw [Finset.sum_congr rfl (fun j _ => by rw [hap j])]
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1 <;> rw [Finset.sum_comm] <;>
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      rw [e]
      have h2 : ∑ q, (lamQ q : ℤ) * b i ≤ ∑ q, (lamQ q : ℤ) * ∑ j, A i j * p q j :=
        Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left ((hpX q).2 i) (by positivity))
      have h3 : 0 ≤ ∑ r, (lamR r : ℤ) * ∑ j, A i j * w r j :=
        Finset.sum_nonneg (fun r _ => mul_nonneg (by positivity) ((hwX r).2 i))
      have h4 : ∑ q, (lamQ q : ℤ) * b i = b i := by
        rw [← Finset.sum_mul]; exact_mod_cast (by rw [h1]; simp : ((∑ q, lamQ q : ℕ) : ℤ) * b i = b i)
      linarith

end Lubbecke2005.Discretization

open Lubbecke2005.Discretization


theorem solution {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ)
    (hP : (polyhedronP D d).Nonempty) :
    ∃ (k l : ℕ) (p : Fin k → (Fin n → ℤ)) (w : Fin l → (Fin n → ℤ)),
      (∀ q, castVec (p q) ∈ integerPoints D d) ∧
      (∀ r, IsIntegerRay D (w r)) ∧
      integerPoints D d =
        {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧
          ∃ (lamQ : Fin k → ℕ) (lamR : Fin l → ℕ),
            ∑ q, lamQ q = 1 ∧
            x = ∑ q, (lamQ q : ℝ) • castVec (p q) + ∑ r, (lamR r : ℝ) • castVec (w r)} := by
  exact discretization_core D d
