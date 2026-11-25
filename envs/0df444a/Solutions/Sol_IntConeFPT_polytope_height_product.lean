-- Prove2me | solution 1 for IntConeFPT.polytope_height_product
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T09:24:28.726352+00:00
-- url     : https://prove2.me/submissions/4b673d78-1c3b-4fe2-a787-e8978bdb1272

import Definitions.Def_IntConeFPT_Instance
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv

open IntConeFPT Matrix LinearOptimization Set
open scoped BigOperators

namespace IntConeFPT.Height

private lemma det_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    |A.det| ≤ ∏ i, ∑ j, |A i j| := by
  classical
  let f := fun (g : Fin n → Fin n) => ∏ i, |A i (g i)|
  let e := fun (σ : Equiv.Perm (Fin n)) => (σ : Fin n → Fin n)
  have inj : Function.Injective e := fun _ _ h => Equiv.ext (congrFun h)
  rw [← Matrix.det_transpose, Matrix.det_apply']
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), f (e σ) := by
      apply Finset.sum_congr rfl; intro σ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, Finset.abs_prod, f, e]
    _ = ∑ g ∈ Finset.univ.image e, f g := (Finset.sum_image inj.injOn).symm
    _ ≤ ∑ g : Fin n → Fin n, f g := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = _ := by simp [Finset.prod_univ_sum, f]

private lemma integer_box {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (R : Fin m → ℕ) (hR : ∀ i, 1 ≤ R i)
    (hrow : ∀ i, (∑ j, |A i j|) + |b i| ≤ R i)
    (P : Set (Fin n → ℝ))
    (heq : P = {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)})
    (hc : IsCompact P) :
    ∀ x ∈ P, ∀ j, |x j| ≤ (∏ i, R i : ℕ) := by
  classical
  let C : Fin m → LinearConstraint n := fun i => ⟨fun j => (A i j : ℝ), b i, .le⟩
  have he : P = constraintSet C := heq
  let r : ℝ := (∏ i, R i : ℕ)
  let box : Set (Fin n → ℝ) := Icc (fun _ => -r) (fun _ => r)
  have hconv : Convex ℝ P := by
    rw [heq]; intro x hx y hy a c ha hc hac i
    change ∑ j, (A i j : ℝ) * (a * x j + c * y j) ≤ _
    calc
      _ = a * (∑ j, (A i j : ℝ) * x j) + c * (∑ j, (A i j : ℝ) * y j) := by
        simp [Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_left_comm]
      _ ≤ a * (b i : ℝ) + c * (b i : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hc)
      _ = _ := by rw [← add_mul, hac, one_mul]
  have hv : P.extremePoints ℝ ⊆ box := by
    intro x hx
    have hxe := hx
    rw [he] at hxe
    have hxC := hxe.1
    have hbasic := ((lp_vertex_extreme_bfs_equiv C x ⟨x,hxC⟩ hxC).out 1 2).mp hxe
    obtain ⟨s, hcard, ht, hi⟩ := hbasic.1.2
    let e : Fin n ≃ s := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
    let S : Matrix (Fin n) (Fin n) ℤ := A.submatrix (fun i => (e i).val) id
    let v : Fin n → ℤ := fun i => b (e i).val
    let T := S.map (Int.castRingHom ℝ)
    have hLI : LinearIndependent ℝ T.row := hi.comp e e.injective
    have hdet : S.det ≠ 0 := by
      have h := ((T.isUnit_iff_isUnit_det).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hLI)).ne_zero
      intro hh
      apply h
      change ((Int.castRingHom ℝ).mapMatrix S).det = 0
      rw [← RingHom.map_det, hh, map_zero]
    have hsys : T *ᵥ x = fun i => (v i : ℝ) := funext fun i => ht _ (e i).property
    have bx (j : Fin n) : |x j| ≤ r := by
      have hid : (((S.updateCol j v).det : ℤ) : ℝ) = (S.det : ℝ) * x j := by
        have hh := congrFun (show T.cramer (T *ᵥ x) = T.det • x by
          rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
            Matrix.smul_mulVec, Matrix.one_mulVec]) j
        rw [hsys, Matrix.cramer_apply] at hh
        convert hh using 1
        · rw [show (((S.updateCol j v).det : ℤ) : ℝ) =
                ((Int.castRingHom ℝ).mapMatrix (S.updateCol j v)).det from (Int.castRingHom ℝ).map_det _]
          congr 1
          ext i l
          by_cases h : l = j <;> simp [h, T]
        · change _ = ((Int.castRingHom ℝ).mapMatrix S).det * x j
          rw [← RingHom.map_det]; rfl
      have hd1 : (1 : ℝ) ≤ |(S.det : ℝ)| := by
        exact_mod_cast (show (1 : ℤ) ≤ |S.det| by have := abs_pos.mpr hdet; omega)
      have hbound (i : Fin n) : (∑ k, |S.updateCol j v i k|) ≤ R (e i).val := by
        refine le_trans ?_ (hrow (e i).val)
        calc
          _ ≤ ∑ k, (|S i k| + if k = j then |v i| else 0) := by
            apply Finset.sum_le_sum; intro k _
            by_cases h : k = j <;> simp [h,abs_nonneg]
          _ = _ := by simp [Finset.sum_add_distrib, S,v]
      have hsize : |(S.updateCol j v).det| ≤ (∏ i, R i : ℕ) := by
        calc
          _ ≤ _ := det_bound _
          _ ≤ ∏ i, (R (e i).val : ℤ) := Finset.prod_le_prod
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (fun i _ => hbound i)
          _ = ∏ i ∈ s, (R i : ℤ) := by
            rw [e.prod_comp (fun i : s => (R i.val : ℤ)), Finset.univ_eq_attach s]
            exact Finset.prod_attach s (fun i => (R i : ℤ))
          _ ≤ ∏ i, (R i : ℤ) := Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
            (fun _ _ => Int.natCast_nonneg _) (fun i _ _ => by exact_mod_cast hR i)
          _ = _ := by simp
      calc
        _ ≤ |(S.det : ℝ)| * |x j| := le_mul_of_one_le_left (abs_nonneg _) hd1
        _ = |(((S.updateCol j v).det : ℤ) : ℝ)| := by rw [hid, abs_mul]
        _ ≤ _ := by dsimp [r]; exact_mod_cast hsize
    exact ⟨fun j => (abs_le.mp (bx j)).1, fun j => (abs_le.mp (bx j)).2⟩
  have hsub : P ⊆ box := by
    rw [← closure_convexHull_extremePoints hc hconv]
    exact closure_minimal (convexHull_min hv (convex_Icc ..)) isClosed_Icc
  exact fun x hx j => abs_le.mpr ⟨(hsub hx).1 j,(hsub hx).2 j⟩

private def H (q : ℚ) := (q.num.natAbs + 1) * q.den

private lemma sum_le {α : Type} (s : Finset α) (f : α → ℕ) :
    1 + (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (f i + 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h := Nat.mul_le_mul_left (f a + 1) ih
    apply le_trans _ h
    rw [Nat.add_mul, Nat.mul_add]
    omega

private def scaled (D : ℕ) (q : ℚ) : ℤ := (D / q.den : ℕ) * q.num

private lemma scaled_cast (D : ℕ) (q : ℚ) (hd : q.den ∣ D) :
    (scaled D q : ℝ) = D * (q : ℝ) := by
  have h : ((D / q.den : ℕ) : ℝ) * q.den = (D : ℝ) := by exact_mod_cast Nat.div_mul_cancel hd
  simp only [scaled, Int.cast_mul, Int.cast_natCast, Rat.cast_def]
  rw [← h]; field_simp

private lemma scaled_abs (D : ℕ) (q : ℚ) : |scaled D q| ≤ ((D * q.num.natAbs : ℕ) : ℤ) := by
  simp only [scaled, abs_mul, abs_of_nonneg (Int.natCast_nonneg _), Nat.cast_mul, Int.natCast_natAbs]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self D q.den) (abs_nonneg _)

private lemma rational_box {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (P : Set (Fin n → ℝ))
    (heq : P = {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)})
    (hc : IsCompact P) :
    ∀ x ∈ P, ∀ j, |x j| ≤ ((∏ i, (∏ j, H (A i j)) * H (b i) : ℕ) : ℝ) := by
  let D := fun i => (∏ j, (A i j).den) * (b i).den
  let R := fun i => (∏ j, H (A i j)) * H (b i)
  have hD i : 0 < D i := Nat.mul_pos (Finset.prod_pos fun _ _ => Rat.pos _) (Rat.pos _)
  have hR i : 1 ≤ R i := Nat.mul_pos (Finset.prod_pos fun _ _ =>
    Nat.mul_pos (Nat.succ_pos _) (Rat.pos _)) (Nat.mul_pos (Nat.succ_pos _) (Rat.pos _))
  let S : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => scaled (D i) (A i j)
  let v := fun i => scaled (D i) (b i)
  have hS i j : (S i j : ℝ) = (D i : ℝ) * A i j :=
    scaled_cast _ _ (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _)
  have hv i : (v i : ℝ) = (D i : ℝ) * b i := scaled_cast _ _ (dvd_mul_left _ _)
  have hrow i : (∑ j, |S i j|) + |v i| ≤ (R i : ℤ) := by
    refine (add_le_add (Finset.sum_le_sum fun j _ => scaled_abs (D i) (A i j)) (scaled_abs (D i) (b i))).trans ?_
    have h := sum_le Finset.univ (fun j => (A i j).num.natAbs)
    have hn : (∑ j, (A i j).num.natAbs) + (b i).num.natAbs ≤
        (∏ j, ((A i j).num.natAbs+1)) * ((b i).num.natAbs+1) := by
      have hh := Nat.mul_le_mul_right ((b i).num.natAbs+1) h
      apply le_trans _ hh
      simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
      omega
    have hres := Nat.mul_le_mul_left (D i) hn
    have hra : R i = D i * ((∏ j, ((A i j).num.natAbs+1)) * ((b i).num.natAbs+1)) := by
      simp only [R, D, H, Finset.prod_mul_distrib]; ring
    rw [hra]
    exact_mod_cast (by simpa [Finset.mul_sum, Nat.mul_add] using hres :
      (∑ j, D i * (A i j).num.natAbs) + D i * (b i).num.natAbs ≤ _)
  apply integer_box S v R hR hrow P _ hc
  rw [heq]
  ext x
  simp only [Set.mem_ofPred_eq,hS,hv,mul_assoc,← Finset.mul_sum]
  exact forall_congr' fun i => (mul_le_mul_iff_right₀ (by exact_mod_cast hD i : 0 < (D i : ℝ))).symm

end IntConeFPT.Height

open IntConeFPT.Height

theorem solution {m d k : ℕ}
    (A : Matrix (Fin m) (Fin d) ℚ) (B : Matrix (Fin m) (Fin k) ℚ) (b : Fin m → ℚ) :
    let P : Set ((Fin d → ℝ) × (Fin k → ℝ)) :=
      {p | ∀ i, (∑ j, (A i j : ℝ) * p.1 j) + (∑ j, (B i j : ℝ) * p.2 j) ≤ (b i : ℝ)}
    let H := fun q : ℚ => (q.num.natAbs + 1) * q.den
    Bornology.IsBounded P → ∀ p ∈ P,
      InBox ((∏ i, ∏ j, H (A i j)) * (∏ i, ∏ j, H (B i j)) * (∏ i, H (b i))) p := by
  intro P Hlocal hbd p hp
  change InBox ((∏ i, ∏ j, H (A i j)) * (∏ i, ∏ j, H (B i j)) * ∏ i, H (b i)) p
  let pack := fun z : (Fin d → ℝ) × (Fin k → ℝ) => Fin.append z.1 z.2
  let S : Matrix (Fin m) (Fin (d+k)) ℚ := Matrix.of fun i => Fin.append (A i) (B i)
  have hclosed : IsClosed P := by
    change IsClosed {p : (Fin d → ℝ) × (Fin k → ℝ) | ∀ i, _}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)
  have hcont : Continuous pack := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [pack]; fun_prop
    · simp [pack]; fun_prop
  have he : pack '' P = {x | ∀ i, ∑ j, (S i j : ℝ) * x j ≤ (b i : ℝ)} := by
    ext x; constructor
    · rintro ⟨w,hw,rfl⟩ i
      simpa [S,pack,Fin.sum_univ_add] using hw i
    · intro hx
      refine ⟨(fun j => x (Fin.castAdd k j), fun j => x (Fin.natAdd d j)), fun i => ?_, ?_⟩
      · simpa [S,Fin.sum_univ_add] using hx i
      · ext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [pack]
  have h := rational_box S b _ he ((Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed,hbd⟩).image hcont)
    (pack p) ⟨p,hp,rfl⟩
  have hsize : (∏ i, (∏ j, H (S i j)) * H (b i)) =
      (∏ i, ∏ j, H (A i j)) * (∏ i, ∏ j, H (B i j)) * ∏ i, H (b i) := by
    simp [S,Fin.prod_univ_add, Finset.prod_mul_distrib]
  rw [hsize] at h
  exact ⟨fun j => by simpa [pack] using h (Fin.castAdd k j),
    fun j => by simpa [pack] using h (Fin.natAdd d j)⟩
