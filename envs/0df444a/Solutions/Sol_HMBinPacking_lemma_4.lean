-- Prove2me | solution 1 for HMBinPacking.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:09:33.585162+00:00
-- url     : https://prove2.me/submissions/5bad54e0-a2ee-4a4d-808e-28d8412c370e

import Mathlib
import Definitions.Def_HMBinPacking_ILP
import Theorems.Thm_HMBinPacking_lemma_2

open HMBinPacking Finset
open scoped Pointwise

private theorem sr_finite (I : Instance) (r : Fin I.d → Fin I.d) : (Sr I r).Finite := by
  apply (Set.Finite.pi (t := fun _ : Fin I.d => Set.Icc (0 : ℤ) I.B)
    (fun _ => Set.finite_Icc _ _)).subset
  intro x hx i _
  obtain ⟨hpos,hcap⟩ := hx.1
  have hpart := Finset.single_le_sum (s := Finset.univ)
    (f := fun i => (I.s i : ℤ) * x i) (fun j _ => mul_nonneg (by positivity) (hpos j))
    (Finset.mem_univ i)
  have hs : (1:ℤ) ≤ I.s i := by exact_mod_cast I.s_pos i
  exact ⟨hpos i, le_trans (by simpa using (mul_le_mul_of_nonneg_right hs (hpos i)) : x i ≤ (I.s i : ℤ)* x i)
    (hpart.trans hcap)⟩

private theorem pr_idp (I : Instance) (r : Fin I.d → Fin I.d) (h : (Sr I r).Nonempty) :
    HasIDP (Pr I r) := by
  classical
  let t : Fin I.d → ℤ := fun i => (r i : ℕ)
  let g : (Fin I.d → ℤ) → Fin I.d → ℤ := fun v i => (v i - t i) / I.d
  let V := g '' Sr I r
  have hn : (I.d:ℤ) ≠ 0 := by exact_mod_cast I.d_pos.ne'
  have hinv (v) (hv : v ∈ Sr I r) : t + (I.d:ℤ) • g v = v := by
    obtain ⟨y,hy⟩ := hv.2
    have he (i) : v i = t i + (I.d : ℤ) * y i := by
      simpa [t,Pi.smul_apply,zsmul_eq_mul] using congrFun hy i
    ext i
    have hg : g v i = y i := by
      change (v i - t i) / (I.d : ℤ) = y i
      rw [he i, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hn]
    change t i + (I.d : ℤ) * g v i = v i
    rw [hg, he i]
  have heq : (fun x => zCast t + x) '' ((I.d : ℝ) • convexHull ℝ (zCast '' V)) = Pr I r := by
    rw [← convexHull_smul]
    change zCast t +ᵥ convexHull ℝ ((I.d : ℝ) • (zCast '' V)) = _
    rw [← convexHull_vadd]
    unfold Pr
    congr 1
    ext x
    have hcast (v) (hv : v ∈ Sr I r) : zCast v = zCast t + (I.d : ℝ) • zCast (g v) := by
      ext i
      have h := congrFun (hinv v hv) i
      simp only [Pi.add_apply,Pi.smul_apply,zsmul_eq_mul] at h
      dsimp [zCast]
      exact_mod_cast h.symm
    constructor
    · rintro ⟨_,⟨_,⟨_,⟨v,hv,rfl⟩,rfl⟩,rfl⟩,rfl⟩
      exact ⟨_,hv,hcast v hv⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨_,⟨_,⟨_,⟨v,hv,rfl⟩,rfl⟩,rfl⟩,(hcast v hv).symm⟩
  rw [← heq]
  simpa using lemma_2 V ((sr_finite I r).image g) (h.image g) (I.d : ℤ) le_rfl t

private theorem integral_pr (I : Instance) (r : Fin I.d → Fin I.d) (x : Fin I.d → ℤ)
    (hx : zCast x ∈ Pr I r) : x ∈ S I := by
  let Q : Set (Fin I.d → ℝ) :=
    {y | (∀ i, 0 ≤ y i) ∧ (∑ i, (I.s i : ℝ)*y i) ≤ I.B}
  have hc : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
    change ∑ i, (I.s i : ℝ) * (a * x i + b * y i) ≤ _
    calc
      _ = a * (∑ i, (I.s i : ℝ) * x i) + b * (∑ i, (I.s i : ℝ) * y i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intros; ring
      _ ≤ a * I.B + b * I.B := by gcongr <;> first | exact hx.2 | exact hy.2
      _ = _ := by rw [← add_mul, hab, one_mul]
  have hsub : zCast '' Sr I r ⊆ Q := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨hpos,hcap⟩ := hz.1
    exact ⟨fun i => by dsimp [zCast]; exact_mod_cast hpos i, by
      change (∑ i, (I.s i:ℝ) * (z i : ℝ)) ≤ _; exact_mod_cast hcap⟩
  have hq := convexHull_min hsub hc hx
  refine ⟨fun i => ?_,?_⟩
  · have h := hq.1 i
    change (0 : ℝ) ≤ (x i : ℝ) at h
    exact_mod_cast h
  · have h := hq.2
    change (∑ i, (I.s i:ℝ) * (x i:ℝ)) ≤ (I.B:ℝ) at h
    exact_mod_cast h

private theorem realize (I : Instance) {J : Type*} [Fintype J] (hcard : Fintype.card J = I.b)
    (p : J → Fin I.d → ℕ) (ha : ∀ i, ∑ j, p j i = I.a i)
    (hc : ∀ j, ∑ i, I.s i * p j i ≤ I.B) : Feasible I := by
  classical
  let e : J ≃ Fin I.b := Fintype.equivOfCardEq (by simpa using hcard)
  let f (i : Fin I.d) : Fin (I.a i) ≃ Σ j : J, Fin (p j i) :=
    Fintype.equivOfCardEq (by simp [ha])
  refine ⟨fun x => e ((f x.1 x.2).1), ?_⟩
  intro l
  obtain ⟨j,rfl⟩ := e.surjective l
  simp only [Finset.sum_filter, Equiv.apply_eq_iff_eq]
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ i, I.s i * p j i := by
      apply Finset.sum_congr rfl; intro i _
      change (∑ x, if (f i x).1 = j then I.s i else 0) = _
      rw [(f i).sum_comp (fun x => if x.1 = j then I.s i else 0)]
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single j]
      · simp [Nat.mul_comm]
      · intro l _ hlj; simp [hlj]
      · simp
    _ ≤ _ := hc j

theorem solution (I : Instance)
    (h : ∃ z : (Fin I.d → Fin I.d) → (Fin I.d → ℤ) × ℤ, castPoint I z ∈ KSet I) :
    Feasible I := by
  classical
  obtain ⟨z, hz, hn, hnon, _, hcone⟩ := h
  let n := fun r => (z r).2.toNat
  have ncast (r) : (n r : ℤ) = (z r).2 := by
    apply Int.toNat_of_nonneg
    have h := (hnon r).1
    change (0 : ℝ) ≤ ((z r).2 : ℝ) at h
    exact_mod_cast h
  have nreal (r) : (n r : ℝ) = ((z r).2 : ℝ) := by exact_mod_cast ncast r
  have hn' : ∑ r,n r = I.b := by
    change (∑ r, ((z r).2 : ℝ)) = (I.b : ℝ) at hn
    simp_rw [← nreal] at hn
    exact_mod_cast hn
  have per_res (r) : ∃ q : Fin (n r) → Fin I.d → ℤ,
      (∀ j, q j ∈ S I) ∧ ∑ j, q j = (z r).1 := by
    rcases hcone r with hzero | ⟨x,hx,N,hN,hpair⟩
    · have eh : castPoint I z r = (0,0) := hzero
      have es := congrArg Prod.snd eh
      have ev := congrArg Prod.fst eh
      change ((z r).2 : ℝ) = 0 at es
      have e0 : n r = 0 := by rw [← nreal] at es; exact_mod_cast es
      have eb : (z r).1 = 0 := by
        ext i
        have hh := congrFun ev i
        change (((z r).1 i : ℤ) : ℝ) = 0 at hh
        exact_mod_cast hh
      rw [e0,eb]
      exact ⟨fun j => Fin.elim0 j, (fun j => Fin.elim0 j), by simp⟩
    · have es := congrArg Prod.snd hpair
      have ev := congrArg Prod.fst hpair
      change ((z r).2 : ℝ) = N at es
      have en := (nreal r).trans es
      have hpos : 0 < n r := by exact_mod_cast (en.symm ▸ hN : (0:ℝ) < (n r:ℝ))
      have hne : (Sr I r).Nonempty := by
        by_contra h
        have he : Sr I r = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        simpa [Pr, he] using hx
      have hmem : zCast (z r).1 ∈ (n r : ℝ) • Pr I r := ⟨x,hx,by rw [en]; exact ev.symm⟩
      obtain ⟨q,hq,hs⟩ := (pr_idp I r hne).2 (n r) hpos (z r).1 hmem
      exact ⟨q,fun j => integral_pr I r _ (hq j), hs⟩
  choose q hq hsum using per_res
  let J := Σ r, Fin (n r)
  let p : J → Fin I.d → ℕ := fun j i => (q j.1 j.2 i).toNat
  have ep (j : J) (i) : (p j i : ℤ) = q j.1 j.2 i := Int.toNat_of_nonneg ((hq _ _).1 i)
  refine realize I (J := J) (by simpa [J] using hn') p ?_ ?_
  · intro i
    have hs (r) : (∑ j, q r j i) = (z r).1 i := by simpa using congrFun (hsum r) i
    have ht := congrFun hz i
    change (∑ r, (castPoint I z r).1) i = (I.a i : ℝ) at ht
    simp [Finset.sum_apply,castPoint,zCast] at ht
    have hzi : (∑ r, (z r).1 i) = (I.a i : ℤ) := by exact_mod_cast ht
    apply Int.ofNat_inj.mp
    push_cast
    change ∑ j : J, (p j i : ℤ) = _
    rw [Fintype.sum_sigma]
    simp only [ep,hs]
    exact hzi
  · intro j
    have hc := (hq j.1 j.2).2
    have h : (∑ i, (I.s i : ℤ) * (p j i : ℤ)) ≤ I.B := by simpa only [ep] using hc
    exact_mod_cast h
