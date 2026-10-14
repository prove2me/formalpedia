-- Prove2me | solution 1 for IntMul.HvdH.exactConv_eq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T02:57:42.41035+00:00
-- url     : https://prove2.me/submissions/a66a3755-f6c4-45a5-aafe-d9be6013b453

import Definitions.Def_IntMul_HvdH_SliceTensor
import Definitions.Def_IntMul_HvdH_ExactConv
import Mathlib
import Theorems.Thm_IntMul_HvdH_mulZ_disc
import Theorems.Thm_IntMul_HvdH_mulZ_err
import Theorems.Thm_IntMul_HvdH_thm_4_1_fp
import Theorems.Thm_IntMul_HvdH_fp_comp

open Finset

namespace IntMul.HvdH.TKer
open IntMul.HvdH

/-- `f` is given by the kernel `K` of width `N`. -/
def Kern (N : ℕ) (K : ℕ → ℕ → ℂ) (f : (ℕ → ℂ) → (ℕ → ℂ)) : Prop :=
  ∀ x n, f x n = ∑ m ∈ range N, K n m * x m

open Classical in
/-- The box with the axes in `l` free (ranging over `range (N i)`) and the others fixed at `J`. -/
noncomputable def pbox {d : ℕ} (N : Fin d → ℕ) (l : List (Fin d)) (J : Fin d → ℕ) :
    Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ l then range (N i) else {J i}

lemma sliceComp_kernel {d : ℕ} (N : Fin d → ℕ) (K : Fin d → ℕ → ℕ → ℂ)
    (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hA : ∀ i, Kern (N i) (K i) (A i)) :
    ∀ (l : List (Fin d)), l.Nodup → ∀ (x : (Fin d → ℕ) → ℂ) (J : Fin d → ℕ),
      sliceComp A l x J = ∑ k ∈ pbox N l J, (∏ i ∈ l.toFinset, K i (J i) (k i)) * x k := by
  classical
  intro l
  induction l with
  | nil =>
    intro _ x J
    have : pbox N [] J = {J} := by
      ext k
      simp only [pbox, List.not_mem_nil, if_false, Fintype.mem_piFinset, mem_singleton]
      exact ⟨fun h => funext h, fun h i => by rw [h]⟩
    simp [sliceComp, this]
  | cons i l ih =>
    intro hnd x J
    have hi : i ∉ l := (List.nodup_cons.1 hnd).1
    have hl : l.Nodup := (List.nodup_cons.1 hnd).2
    simp only [sliceComp, Function.comp]
    rw [ih hl]
    -- expand the slice map
    have hy : ∀ k ∈ pbox N l J, sliceMap i (A i) x k =
        ∑ m ∈ range (N i), K i (J i) m * x (Function.update k i m) := by
      intro k hk
      have hki : k i = J i := by
        have := Fintype.mem_piFinset.1 hk i
        simp only [hi, if_false, mem_singleton] at this; exact this
      unfold sliceMap; rw [hA i, hki]
    rw [Finset.sum_congr rfl (fun k hk => by rw [hy k hk])]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    refine Finset.sum_nbij' (fun k => (Function.update k i (J i), k i))
      (fun km => Function.update km.1 i km.2) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' := Fintype.mem_piFinset.1 hk
      simp only [mem_product, pbox, Fintype.mem_piFinset]
      refine ⟨fun i' => ?_, ?_⟩
      · by_cases h : i' = i
        · subst h; simp [hi]
        · rw [Function.update_of_ne h]
          have := hk' i'
          simp only [List.mem_cons, h, false_or] at this
          exact this
      · have := hk' i; simpa using this
    · intro km hkm
      simp only [mem_product, pbox, Fintype.mem_piFinset] at hkm
      simp only [pbox, Fintype.mem_piFinset]
      intro i'
      by_cases h : i' = i
      · subst h; simp [hkm.2]
      · rw [Function.update_of_ne h]
        have := hkm.1 i'
        simpa [List.mem_cons, h] using this
    · intro k hk
      simp
    · intro km hkm
      simp only [mem_product, pbox, Fintype.mem_piFinset] at hkm
      have : km.1 i = J i := by have := hkm.1 i; simpa [hi] using this
      ext i' <;> simp
      · by_cases h : i' = i
        · subst h; simp [this]
        · simp [Function.update_of_ne h]
    · intro k hk
      simp only
      have hprod : ∏ i' ∈ (i :: l).toFinset, K i' (J i') (k i') =
          K i (J i) (k i) * ∏ i' ∈ l.toFinset, K i' (J i') (Function.update k i (J i) i') := by
        rw [List.toFinset_cons, Finset.prod_insert (by simpa using hi)]
        congr 1
        apply Finset.prod_congr rfl
        intro i' hi'
        have : i' ≠ i := fun h => hi (h ▸ List.mem_toFinset.1 hi')
        rw [Function.update_of_ne this]
      rw [hprod, Function.update_idem, Function.update_eq_self]
      ring

/-- A tensor product of kernel maps is the box sum with the product kernel. -/
theorem tensorMap_kernel {d : ℕ} (N : Fin d → ℕ) (K : Fin d → ℕ → ℕ → ℂ)
    (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hA : ∀ i, Kern (N i) (K i) (A i))
    (x : (Fin d → ℕ) → ℂ) (J : Fin d → ℕ) :
    tensorMap A x J = ∑ k ∈ Fintype.piFinset (fun i => range (N i)),
      (∏ i, K i (J i) (k i)) * x k := by
  classical
  unfold tensorMap
  rw [sliceComp_kernel N K A hA _ (List.nodup_finRange d)]
  have h1 : pbox N (List.finRange d) J = Fintype.piFinset (fun i => range (N i)) := by
    simp [pbox]
  have h2 : (List.finRange d).toFinset = Finset.univ := by ext; simp
  rw [h1, h2]

end IntMul.HvdH.TKer


open Finset Complex

namespace IntMul.HvdH.ExId
open IntMul.HvdH IntMul.HvdH.TKer

/-- `ω_N = e^{2πi/N}`. -/
noncomputable def om (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma stdAddChar_nat (N : ℕ) [NeZero N] (a b : ℕ) :
    (ZMod.stdAddChar (-((a : ZMod N) * (b : ZMod N))) : ℂ) = om N ^ (-((a * b : ℕ) : ℤ)) := by
  rw [ZMod.stdAddChar_apply, show -((a : ZMod N) * (b : ZMod N)) = ((-((a * b : ℕ) : ℤ) : ℤ) : ZMod N) by
    push_cast; ring, ZMod.toCircle_intCast, om, ← Complex.exp_int_mul]
  congr 1; ring

lemma sum_zmod (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    ∑ j : ZMod N, f j = ∑ m ∈ range N, f (m : ZMod N) := by
  refine Finset.sum_nbij' (fun j => j.val) (fun m => (m : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro j _; simp [ZMod.val_lt]
  · intro m _; simp
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro m hm; exact ZMod.val_natCast_of_lt (by simpa using hm)
  · intro j _; simp

/-- The kernel of a linear map between `ZMod` function spaces, read on `ℕ`-indexed vectors. -/
lemma kern_zmod (s t : ℕ) [NeZero s] (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) :
    Kern s (fun k m => A (Pi.single (m : ZMod s) 1) (k : ZMod t))
      (fun x k => A (fun j => x j.val) (k : ZMod t)) := by
  intro x k
  have hx : (fun j : ZMod s => x j.val) = ∑ m ∈ range s, x m • Pi.single (m : ZMod s) (1 : ℂ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j.val]
    · simp
    · intro m hm hne
      have : (m : ZMod s) ≠ j := by
        intro h; apply hne; rw [← h, ZMod.val_natCast_of_lt (Finset.mem_range.1 hm)]
      simp [Pi.single_apply, this.symm]
    · intro h; exact absurd (Finset.mem_range.2 (ZMod.val_lt j)) h
  simp only
  rw [hx, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- The one-dimensional normalised DFT kernel on `[0, t)`, zero outside. -/
noncomputable def KD (t : ℕ) (k m : ℕ) : ℂ :=
  if k < t then (1 / (t : ℂ)) * om t ^ (-((k * m : ℕ) : ℤ)) else 0

noncomputable def D1 (t : ℕ) (x : ℕ → ℂ) (k : ℕ) : ℂ := ∑ m ∈ range t, KD t k m * x m

lemma dftBox_eq {d : ℕ} (t : Fin d → ℕ) (x : (Fin d → ℕ) → ℂ) :
    dftBox t x = tensorMap (fun i => D1 (t i)) x := by
  classical
  funext J
  rw [tensorMap_kernel t (fun i => KD (t i)) (fun i => D1 (t i)) (fun i x k => rfl)]
  unfold dftBox KD
  simp_rw [Finset.prod_ite_zero]
  by_cases h : ∀ i, J i < t i
  · simp only [Finset.mem_univ, true_implies, h, implies_true, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.prod_mul_distrib, ← mul_assoc, Finset.prod_div_distrib, Finset.prod_const_one]
    rfl
  · have h' : ¬ ∀ i ∈ Finset.univ, J i < t i := by simpa using h
    simp only [h, h', if_false, zero_mul, Finset.sum_const_zero]

/-- The scaled one-dimensional resampling identity in kernel form. -/
lemma kernel_id (s t α : ℕ) [NeZero s] [NeZero t]
    (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hF : ∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u)))
    (J l : ℕ) (hJ : J < s) (hl : l < s) :
    ∑ k ∈ range t, B (Pi.single (k : ZMod t) 1) (J : ZMod s) *
      ∑ m ∈ range t, KD t k m * A (Pi.single (l : ZMod s) 1) (m : ZMod t) =
      ((2 : ℂ) ^ (2 * α ^ 2))⁻¹ * ((1 / (s : ℂ)) * om s ^ (-((J * l : ℕ) : ℤ))) := by
  have h := congrFun (hF (Pi.single (l : ZMod s) 1)) (J : ZMod s)
  rw [Pi.smul_apply, ZMod.dft_apply, sum_zmod] at h
  rw [Finset.sum_eq_single l] at h
  rotate_left
  · intro m hm hne
    have : (m : ZMod s) ≠ (l : ZMod s) := by
      intro h'; apply hne
      have := congrArg ZMod.val h'
      rwa [ZMod.val_natCast_of_lt (Finset.mem_range.1 hm), ZMod.val_natCast_of_lt hl] at this
    simp [Pi.single_apply, this]
  · intro h'; exact absurd (Finset.mem_range.2 hl) h'
  simp only [Pi.single_eq_same, smul_eq_mul, mul_one] at h
  rw [stdAddChar_nat] at h
  -- right-hand side through the kernel of `B`
  have hB := kern_zmod t s B (fun k => ((t : ℂ)⁻¹ • ZMod.dft (A (Pi.single (l : ZMod s) 1)))
    (k : ZMod t)) J
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at hB
  rw [Pi.smul_apply, smul_eq_mul, hB] at h
  have hy : ∀ k ∈ range t, ((t : ℂ)⁻¹ • ZMod.dft (A (Pi.single (l : ZMod s) 1))) (k : ZMod t) =
      ∑ m ∈ range t, KD t k m * A (Pi.single (l : ZMod s) 1) (m : ZMod t) := by
    intro k hk
    rw [Pi.smul_apply, ZMod.dft_apply, sum_zmod, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [stdAddChar_nat, KD, if_pos (Finset.mem_range.1 hk), smul_eq_mul, mul_comm m k]
    ring
  rw [Finset.sum_congr rfl (fun k hk => by rw [hy k hk])] at h
  have h2 : (2 : ℂ) ^ (2 * α ^ 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [eq_inv_mul_iff_mul_eq₀ h2, ← h, mul_comm J l, one_div]

/-- **Multidimensional resampling identity** `B ∘ 𝓕_t ∘ A = 2^{-2dα²} 𝓕_s` on the box `s`, for the
tensor products of the one-dimensional maps of Theorem 4.1. -/
theorem resample_id {d : ℕ} (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] (α : ℕ)
    (A : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (t i) → ℂ))
    (B : ∀ i, (ZMod (t i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hF : ∀ i u, (s i : ℂ)⁻¹ • ZMod.dft u =
      (2 : ℂ) ^ (2 * α ^ 2) • B i ((t i : ℂ)⁻¹ • ZMod.dft (A i u)))
    (x : (Fin d → ℕ) → ℂ) (J : Fin d → ℕ) (hJ : ∀ i, J i < s i) :
    tensorMap (fun i (y : ℕ → ℂ) (j : ℕ) => B i (fun k => y k.val) (j : ZMod (s i)))
      (dftBox t (tensorMap (fun i (y : ℕ → ℂ) (k : ℕ) => A i (fun j => y j.val) (k : ZMod (t i))) x)) J
      = ((2 : ℂ) ^ (2 * α ^ 2))⁻¹ ^ d * dftBox s x J := by
  classical
  set KA : Fin d → ℕ → ℕ → ℂ := fun i k m => A i (Pi.single (m : ZMod (s i)) 1) (k : ZMod (t i))
  set KB : Fin d → ℕ → ℕ → ℂ := fun i k m => B i (Pi.single (m : ZMod (t i)) 1) (k : ZMod (s i))
  set c : ℂ := ((2 : ℂ) ^ (2 * α ^ 2))⁻¹
  have hA : ∀ y m, tensorMap (fun i (y : ℕ → ℂ) (k : ℕ) => A i (fun j => y j.val) (k : ZMod (t i))) y m =
      ∑ l ∈ Fintype.piFinset (fun i => range (s i)), (∏ i, KA i (m i) (l i)) * y l :=
    fun y m => tensorMap_kernel s KA _ (fun i => kern_zmod (s i) (t i) (A i)) y m
  have hD : ∀ y m, dftBox t y m =
      ∑ k ∈ Fintype.piFinset (fun i => range (t i)), (∏ i, KD (t i) (m i) (k i)) * y k := by
    intro y m
    rw [dftBox_eq]; exact tensorMap_kernel t (fun i => KD (t i)) _ (fun i x k => rfl) y m
  rw [tensorMap_kernel t KB _ (fun i => kern_zmod (t i) (s i) (B i))]
  simp_rw [hD, hA]
  -- right-hand side as a kernel sum
  have hR : c ^ d * dftBox s x J = ∑ l ∈ Fintype.piFinset (fun i => range (s i)),
      (∏ i, ∑ k ∈ range (t i), KB i (J i) k * ∑ m ∈ range (t i), KD (t i) k m * KA i m (l i)) * x l := by
    unfold dftBox
    rw [if_pos hJ, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' : ∀ i, l i < s i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hl i)
    rw [← mul_assoc]
    congr 1
    rw [Finset.prod_congr rfl (fun i _ => kernel_id (s i) (t i) α (A i) (B i) (hF i) (J i) (l i) (hJ i) (hl' i))]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_div_distrib, Finset.prod_const_one]
    simp only [c, om]; ring
  rw [hR]
  -- expand the products of sums
  have hP : ∀ l : Fin d → ℕ, (∏ i, ∑ k ∈ range (t i), KB i (J i) k *
      ∑ m ∈ range (t i), KD (t i) k m * KA i m (l i)) =
      ∑ k ∈ Fintype.piFinset (fun i => range (t i)), (∏ i, KB i (J i) (k i)) *
        ∑ m ∈ Fintype.piFinset (fun i => range (t i)),
          (∏ i, KD (t i) (k i) (m i)) * ∏ i, KA i (m i) (l i) := by
    intro l
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.prod_mul_distrib, Finset.prod_univ_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.prod_mul_distrib]
  simp_rw [hP, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro l _
  ring

end IntMul.HvdH.ExId


open Finset

namespace IntMul.HvdH.BoxConv

theorem box_conv {d : ℕ} (t : Fin d → ℕ) (W : Fin d → ℂ) (hW0 : ∀ i, W i ≠ 0)
    (horth : ∀ i (a : ℤ), ∑ m ∈ Finset.range (t i), W i ^ ((m : ℤ) * a) =
      if (t i : ℤ) ∣ a then (t i : ℂ) else 0)
    (U V : (Fin d → ℕ) → ℂ) (k : Fin d → ℕ) (hk : ∀ i, k i < t i) :
    ∑ m ∈ Fintype.piFinset (fun i => Finset.range (t i)),
      (∏ i, W i ^ ((k i * m i : ℕ) : ℤ)) *
        ((∑ n ∈ Fintype.piFinset (fun i => Finset.range (t i)),
            (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * U n) *
          (∑ n ∈ Fintype.piFinset (fun i => Finset.range (t i)),
            (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * V n)) =
      (∏ i, (t i : ℂ)) * ∑ n ∈ Fintype.piFinset (fun i => Finset.range (t i)),
        U n * V (fun i => (k i + t i - n i) % t i) := by
  classical
  set box := Fintype.piFinset (fun i => Finset.range (t i))
  -- expand everything into a triple sum
  have h1 : ∀ m : Fin d → ℕ, (∏ i, W i ^ ((k i * m i : ℕ) : ℤ)) *
      ((∑ n ∈ box, (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * U n) *
        (∑ n ∈ box, (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * V n)) =
      ∑ n ∈ box, ∑ n' ∈ box, U n * V n' *
        ∏ i, W i ^ ((m i : ℤ) * ((k i : ℤ) - n i - n' i)) := by
    intro m
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _
    have : ∏ i, W i ^ ((m i : ℤ) * ((k i : ℤ) - n i - n' i)) =
        (∏ i, W i ^ ((k i * m i : ℕ) : ℤ)) * (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) *
          (∏ i, W i ^ (-((m i * n' i : ℕ) : ℤ))) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rw [← zpow_add₀ (hW0 i), ← zpow_add₀ (hW0 i)]
      congr 1; push_cast; ring
    rw [this]; ring
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n hn
  rw [Finset.sum_comm]
  have h2 : ∀ n' ∈ box, ∑ m ∈ box, U n * V n' * ∏ i, W i ^ ((m i : ℤ) * ((k i : ℤ) - n i - n' i)) =
      U n * V n' * (if ∀ i, (t i : ℤ) ∣ ((k i : ℤ) - n i - n' i) then ∏ i, (t i : ℂ) else 0) := by
    intro n' _
    rw [← Finset.mul_sum]
    congr 1
    rw [show box = Fintype.piFinset (fun i => Finset.range (t i)) from rfl,
      ← Finset.prod_univ_sum (fun i => Finset.range (t i))
        (fun i mi => W i ^ ((mi : ℤ) * ((k i : ℤ) - n i - n' i)))]
    simp only [horth]
    rw [Fintype.prod_ite_zero (p := fun i => (t i : ℤ) ∣ ((k i : ℤ) - n i - n' i))
      (f := fun i => (t i : ℂ))]
    congr 1
  rw [Finset.sum_congr rfl h2]
  set tgt : Fin d → ℕ := fun i => (k i + t i - n i) % t i
  have hn' : ∀ i, n i < t i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hn i)
  have hiff : ∀ n' ∈ box, (∀ i, (t i : ℤ) ∣ ((k i : ℤ) - n i - n' i)) ↔ n' = tgt := by
    intro n' hn'b
    have hb : ∀ i, n' i < t i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hn'b i)
    constructor
    · intro h; funext i
      have := h i
      simp only [tgt]
      have hti : 0 < t i := by have := hk i; omega
      rw [Int.dvd_iff_emod_eq_zero] at this
      have e1 : ((k i + t i - n i : ℕ) : ℤ) = (k i : ℤ) + t i - n i := by
        rw [Nat.cast_sub (show n i ≤ k i + t i by have := hn' i; omega)]; push_cast; ring
      zify
      rw [e1]
      have hlt : (n' i : ℤ) < t i := by exact_mod_cast hb i
      have h0 : (0 : ℤ) ≤ n' i := by positivity
      rw [show (k i : ℤ) + t i - n i = n' i + ((k i - n i - n' i) + t i) by ring,
        Int.add_emod, show ((k i : ℤ) - n i - n' i + t i) % t i = 0 by
          rw [Int.add_emod_right]; exact this]
      simp [Int.emod_eq_of_lt h0 hlt]
    · rintro rfl i
      simp only [tgt]
      have hti : 0 < t i := by have := hk i; omega
      rw [Int.dvd_iff_emod_eq_zero]
      push_cast [Nat.cast_sub (show n i ≤ k i + t i by have := hn' i; omega)]
      rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod]
      rw [show (k i : ℤ) - n i - (k i + t i - n i) = -1 * t i by ring, Int.mul_emod_left]
  have htgt : tgt ∈ box := by
    rw [Fintype.mem_piFinset]; intro i
    have hti : 0 < t i := by have := hk i; omega
    exact Finset.mem_range.2 (Nat.mod_lt _ hti)
  rw [Finset.sum_congr rfl (fun n' hn'b => by rw [if_congr (hiff n' hn'b) rfl rfl])]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' box tgt, if_pos htgt]
  ring

/-! ### The convolution identity over `R` -/


end IntMul.HvdH.BoxConv

namespace IntMul.HvdH.BoxConv
open Complex

lemma horth_om (N : ℕ) (hN : 0 < N) (a : ℤ) :
    ∑ m ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I / N) ^ ((m : ℤ) * a) =
      if (N : ℤ) ∣ a then (N : ℂ) else 0 := by
  have hp := Complex.isPrimitiveRoot_exp N hN.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / N)
  have h1 : ∀ m : ℕ, ζ ^ ((m : ℤ) * a) = (ζ ^ a) ^ m := by
    intro m; rw [mul_comm, zpow_mul, zpow_natCast]
  simp_rw [h1]
  split_ifs with h
  · rw [(hp.zpow_eq_one_iff_dvd a).2 h]; simp
  · have hne : ζ ^ a ≠ 1 := fun h' => h ((hp.zpow_eq_one_iff_dvd a).1 h')
    rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hp.pow_eq_one, one_zpow, sub_self, zero_div]

lemma om_ne_zero (N : ℕ) : Complex.exp (2 * Real.pi * Complex.I / N) ≠ 0 := Complex.exp_ne_zero _

lemma conj_om_zpow (N : ℕ) (a : ℤ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I / N) ^ a) =
      Complex.exp (2 * Real.pi * Complex.I / N) ^ (-a) := by
  have h : (starRingEnd ℂ) (2 * Real.pi * Complex.I / N) = -(2 * Real.pi * Complex.I / N) := by
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]; ring
  rw [map_zpow₀, ← Complex.exp_conj, h, Complex.exp_neg, inv_zpow, zpow_neg]

end IntMul.HvdH.BoxConv


open Finset Complex

namespace IntMul.HvdH.ExPf
open IntMul.HvdH IntMul.HvdH.TKer IntMul.HvdH.ExId IntMul.HvdH.BoxConv

lemma dftBox_in {d : ℕ} (t : Fin d → ℕ) (x : (Fin d → ℕ) → ℂ) (j : Fin d → ℕ) (hj : ∀ i, j i < t i) :
    dftBox t x j = (1 / ∏ i, (t i : ℂ)) * ∑ k ∈ Fintype.piFinset (fun i => Finset.range (t i)),
      (∏ i, Complex.exp (2 * Real.pi * Complex.I / t i) ^ (-((j i * k i : ℕ) : ℤ))) * x k := by
  unfold dftBox; rw [if_pos hj]

/-- Cyclic convolution through two forward transforms:
`u * v = S² · conj(𝓕_s(conj(𝓕_s u · 𝓕_s v)))` on the box. -/
lemma conv_id {d : ℕ} (s : Fin d → ℕ) (hs : ∀ i, 0 < s i) (u v : (Fin d → ℕ) → ℂ)
    (j : Fin d → ℕ) (hj : ∀ i, j i < s i) :
    (∏ i, (s i : ℂ)) ^ 2 * (starRingEnd ℂ)
        (dftBox s (fun m => (starRingEnd ℂ) (dftBox s u m * dftBox s v m)) j) =
      ∑ n ∈ Fintype.piFinset (fun i => range (s i)), u n * v (fun i => (j i + s i - n i) % s i) := by
  classical
  set S : ℂ := ∏ i, (s i : ℂ)
  have hS : S ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => by exact_mod_cast (hs i).ne')
  set W : Fin d → ℂ := fun i => Complex.exp (2 * Real.pi * Complex.I / s i)
  set Fu : (Fin d → ℕ) → ℂ := fun m => ∑ n ∈ Fintype.piFinset (fun i => range (s i)),
    (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * u n
  set Fv : (Fin d → ℕ) → ℂ := fun m => ∑ n ∈ Fintype.piFinset (fun i => range (s i)),
    (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * v n
  have hY : ∀ m ∈ Fintype.piFinset (fun i => range (s i)),
      dftBox s u m * dftBox s v m = (1 / S) ^ 2 * (Fu m * Fv m) := by
    intro m hm
    have hm' : ∀ i, m i < s i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hm i)
    rw [dftBox_in s u m hm', dftBox_in s v m hm']
    ring
  have hbc := box_conv s W (fun i => Complex.exp_ne_zero _)
    (fun i a => horth_om (s i) (hs i) a) u v j hj
  rw [dftBox_in s _ j hj]
  have hconjS : (starRingEnd ℂ) (1 / S) = 1 / S := by
    simp only [S, map_div₀, map_one, map_prod, map_natCast]
  rw [map_mul, hconjS, map_sum]
  have hterm : ∀ m ∈ Fintype.piFinset (fun i => range (s i)),
      (starRingEnd ℂ) ((∏ i, Complex.exp (2 * Real.pi * Complex.I / s i) ^ (-((j i * m i : ℕ) : ℤ))) *
        (starRingEnd ℂ) (dftBox s u m * dftBox s v m)) =
      (1 / S) ^ 2 * ((∏ i, W i ^ ((j i * m i : ℕ) : ℤ)) * (Fu m * Fv m)) := by
    intro m hm
    rw [map_mul, Complex.conj_conj, map_prod, hY m hm]
    simp_rw [conj_om_zpow, neg_neg]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hbc]
  simp only [S] at hS ⊢
  field_simp

end IntMul.HvdH.ExPf


open Finset Complex

namespace IntMul.HvdH.ExMain
open IntMul.HvdH IntMul.HvdH.TKer IntMul.HvdH.ExId IntMul.HvdH.BoxConv IntMul.HvdH.ExPf

lemma gC_conjZ (z : ℤ × ℤ) : gC (conjZ z) = (starRingEnd ℂ) (gC z) := by
  simp [gC, conjZ, map_add, map_mul, Complex.conj_I]

lemma conj_err (p : ℕ) (z : ℤ × ℤ) (w : ℂ) :
    ‖gC (conjZ z) - 2 ^ p * (starRingEnd ℂ) w‖ = ‖gC z - 2 ^ p * w‖ := by
  rw [gC_conjZ, show (2 : ℂ) ^ p * (starRingEnd ℂ) w = (starRingEnd ℂ) (2 ^ p * w) by
    rw [map_mul, map_pow, map_ofNat], ← map_sub, Complex.norm_conj]

lemma norm_om_zpow (N : ℕ) (a : ℤ) : ‖Complex.exp (2 * Real.pi * Complex.I / N) ^ a‖ = 1 := by
  rw [norm_zpow, show 2 * Real.pi * Complex.I / (N : ℂ) = ((2 * Real.pi / N : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_zpow]

lemma dftBox_congr {d : ℕ} (t : Fin d → ℕ) (x y : (Fin d → ℕ) → ℂ)
    (h : ∀ m, (∀ i, m i < t i) → x m = y m) (j : Fin d → ℕ) : dftBox t x j = dftBox t y j := by
  by_cases hj : ∀ i, j i < t i
  · rw [dftBox_in t x j hj, dftBox_in t y j hj]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [h k (fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hk i))]
  · unfold dftBox; rw [if_neg hj, if_neg hj]

lemma dftBox_smul {d : ℕ} (t : Fin d → ℕ) (a : ℂ) (x : (Fin d → ℕ) → ℂ) (j : Fin d → ℕ) :
    dftBox t (fun m => a * x m) j = a * dftBox t x j := by
  unfold dftBox
  split_ifs
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  · ring

lemma dftBox_lip {d : ℕ} (t : Fin d → ℕ) : SupLip (dftBox t) := by
  intro x y δ h j
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (h j)
  by_cases hj : ∀ i, j i < t i
  · rw [dftBox_in t x j hj, dftBox_in t y j hj, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
    have hT : (0 : ℝ) ≤ ∏ i, (t i : ℝ) := by positivity
    have hs : ‖∑ k ∈ Fintype.piFinset (fun i => range (t i)),
        ((∏ i, Complex.exp (2 * Real.pi * Complex.I / t i) ^ (-((j i * k i : ℕ) : ℤ))) * x k -
         (∏ i, Complex.exp (2 * Real.pi * Complex.I / t i) ^ (-((j i * k i : ℕ) : ℤ))) * y k)‖ ≤
        (∏ i, (t i : ℝ)) * δ := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ k ∈ Fintype.piFinset (fun i => range (t i)),
          ‖(∏ i, Complex.exp (2 * Real.pi * Complex.I / t i) ^ (-((j i * k i : ℕ) : ℤ))) * x k -
           (∏ i, Complex.exp (2 * Real.pi * Complex.I / t i) ^ (-((j i * k i : ℕ) : ℤ))) * y k‖ ≤ δ := by
        intro k _
        rw [← mul_sub, norm_mul, norm_prod]
        simp_rw [norm_om_zpow]
        rw [Finset.prod_const_one, one_mul]; exact h k
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul]
      simp
    by_cases hz : ∏ i, (t i : ℝ) = 0
    · have : ∏ i, (t i : ℂ) = 0 := by exact_mod_cast hz
      rw [this]; simp [hδ]
    · calc _ ≤ ‖(1 / ∏ i, (t i : ℂ))‖ * ((∏ i, (t i : ℝ)) * δ) :=
            mul_le_mul_of_nonneg_left hs (norm_nonneg _)
        _ = δ := by
          rw [norm_div, norm_one, norm_prod]; simp only [Complex.norm_natCast]
          field_simp
  · unfold dftBox; rw [if_neg hj, if_neg hj]; simpa using hδ

lemma tensor_zero {d : ℕ} (N : Fin d → ℕ) (K : Fin d → ℕ → ℕ → ℂ)
    (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hA : ∀ i, Kern (N i) (K i) (A i)) :
    tensorMap A (fun _ => 0) = fun _ => 0 := by
  funext J; rw [tensorMap_kernel N K A hA]; simp

lemma lip_bound {ι κ : Type*} (R : (ι → ℂ) → (κ → ℂ)) (hR : SupLip R) (h0 : R (fun _ => 0) = fun _ => 0)
    (x : ι → ℂ) (hx : ∀ i, ‖x i‖ ≤ 1) (k : κ) : ‖R x k‖ ≤ 1 := by
  have := hR x (fun _ => 0) 1 (fun i => by simpa using hx i) k
  rwa [h0, sub_zero] at this

lemma roundDiv_eq (a w : ℤ) (m : ℕ) (hm : 0 < m) (h : 2 * |a - w * m| < m) : roundDiv a m = w := by
  unfold roundDiv
  have h1 := abs_lt.1 (show |2 * (a - w * m)| < m by rw [abs_mul]; simpa using h)
  have hm' : (0 : ℤ) < 2 * m := by positivity
  rw [show 2 * a + (m : ℤ) = (2 * a + m - 2 * m * w) + 2 * m * w by ring,
    Int.add_mul_ediv_left _ _ hm'.ne', Int.ediv_eq_zero_of_lt (by linarith) (by linarith), zero_add]

/-- **Exactness of the convolution pipeline** (Harvey–van der Hoeven §5.3 with an arbitrary
fixed-point oracle `Ft` for the DFT on the power-of-two box `t`). -/
theorem exactConv_eq {d : ℕ} (p α b : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : ∀ i, s i ≤ α ^ 2 * (t i - s i))
    (hp : ∀ i, 100 * (jIter p (s i) (t i) α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p)
    (Ft : ((Fin d → ℕ) → ℤ × ℤ) → ((Fin d → ℕ) → ℤ × ℤ)) (εF : ℝ)
    (hFt : ∀ U : (Fin d → ℕ) → ℤ × ℤ, InDisc p U → ∀ j : Fin d → ℕ, (∀ i, j i < t i) →
      ‖gC (Ft U j)‖ ≤ 2 ^ p ∧
      ‖gC (Ft U j) - 2 ^ p * dftBox t (fun x => gC (U x) / 2 ^ p) j‖ ≤ εF)
    (hb : b ≤ p) (u v : (Fin d → ℕ) → ℤ) (hu : ∀ x, |u x| < 2 ^ b) (hv : ∀ x, |v x| < 2 ^ b)
    (hprec : 2 * (3 * ((∑ _i : Fin d, (6 * sWidth p α + 4 : ℝ)) + εF +
        ∑ i, ((jIter p (s i) (t i) α : ℝ) * (10 * eWidth p α + 12) + 4)) + 2) *
        ((∏ i, s i : ℕ) : ℝ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2) < 2 ^ p) :
    ∀ j : Fin d → ℕ, (∀ i, j i < s i) → exactConv p α b s t Ft u v j = convBox s u v j := by
  classical
  obtain ⟨A, B, hAB, hSa, hBa, hLA, hLB⟩ :=
    thm_4_1_fp p α s t hst hcop hα hαp hx hp hpA
  set Am := tensorMap fun i (x : ℕ → ℂ) (k : ℕ) => A i (fun j => x j.val) (k : ZMod (t i))
  set Bm := tensorMap fun i (x : ℕ → ℂ) (j : ℕ) => B i (fun k => x k.val) (j : ZMod (s i))
  set εA : ℝ := ∑ _i : Fin d, (6 * sWidth p α + 4 : ℝ)
  set εB : ℝ := ∑ i, ((jIter p (s i) (t i) α : ℝ) * (10 * eWidth p α + 12) + 4)
  set E : ℝ := εA + εF + εB
  have hP : (0 : ℝ) < 2 ^ p := by positivity
  have hpC : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  -- the oracle stage
  have hεF : 0 ≤ εF := by
    have := (hFt (fun _ => (0, 0)) (fun _ => by simp [gC]) (fun _ => 0)
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (t i)))).2
    exact (norm_nonneg _).trans this
  have hD : FPApprox p (maskZ t ∘ Ft) (dftBox t) εF := by
    intro U hU
    refine ⟨fun j => ?_, fun j => ?_⟩
    · simp only [Function.comp, maskZ]
      split_ifs with h
      · exact (hFt U hU j h).1
      · simp [gC]
    · simp only [Function.comp, maskZ]
      split_ifs with h
      · exact (hFt U hU j h).2
      · unfold dftBox; rw [if_neg h]; simpa [gC] using hεF
  have hfwd : FPApprox p (fwdZ p α s t Ft) (Bm ∘ dftBox t ∘ Am) E := by
    have h1 := fp_comp p (fp_comp p hSa hD (dftBox_lip t)) hBa hLB
    exact h1
  set R := Bm ∘ dftBox t ∘ Am
  have hRlip : SupLip R := by
    intro x y δ h k
    exact hLB _ _ δ (dftBox_lip t _ _ δ (hLA x y δ h)) k
  have hR0 : R (fun _ => 0) = fun _ => 0 := by
    have hA0 : Am (fun _ => 0) = fun _ => 0 :=
      tensor_zero s _ _ (fun i => kern_zmod (s i) (t i) (A i))
    have hB0 : Bm (fun _ => 0) = fun _ => 0 :=
      tensor_zero t _ _ (fun i => kern_zmod (t i) (s i) (B i))
    have hD0 : dftBox t (fun _ => 0) = fun _ => (0 : ℂ) := by
      funext j; unfold dftBox; split_ifs <;> simp
    simp only [R, Function.comp, hA0, hD0, hB0]
  have hRid : ∀ x j, (∀ i, j i < s i) →
      R x j = ((2 : ℂ) ^ (2 * α ^ 2))⁻¹ ^ d * dftBox s x j := fun x j hj =>
    resample_id s t α A B (fun i => (hAB i).2.2) x j hj
  -- inputs
  have hbP : (2 : ℝ) ^ b * 2 ^ (p - b) = 2 ^ p := by rw [← pow_add, Nat.add_sub_cancel' hb]
  set u' : (Fin d → ℕ) → ℂ := fun x => (u x : ℂ) / 2 ^ b
  set v' : (Fin d → ℕ) → ℂ := fun x => (v x : ℂ) / 2 ^ b
  set U : (Fin d → ℕ) → ℤ × ℤ := fun x => (u x * 2 ^ (p - b), 0)
  set V : (Fin d → ℕ) → ℤ × ℤ := fun x => (v x * 2 ^ (p - b), 0)
  have hgU : ∀ (w : (Fin d → ℕ) → ℤ) x, gC ((fun x => (w x * 2 ^ (p - b), (0 : ℤ))) x) / 2 ^ p =
      (w x : ℂ) / 2 ^ b := by
    intro w x
    simp only [gC]; push_cast
    rw [zero_mul, add_zero, show (2 : ℂ) ^ p = 2 ^ b * 2 ^ (p - b) by
      rw [← pow_add, Nat.add_sub_cancel' hb]]
    field_simp
  have hdiscI : ∀ (w : (Fin d → ℕ) → ℤ), (∀ x, |w x| < 2 ^ b) →
      InDisc p (fun x => (w x * 2 ^ (p - b), (0 : ℤ))) := by
    intro w hw x
    simp only [gC]; push_cast
    rw [zero_mul, add_zero, norm_mul, Complex.norm_intCast, norm_pow, Complex.norm_two, ← hbP]
    have : (|w x| : ℝ) < 2 ^ b := by exact_mod_cast hw x
    exact mul_le_mul_of_nonneg_right this.le (by positivity)
  have hu1 : ∀ x, ‖u' x‖ ≤ 1 := fun x => by
    show ‖(u x : ℂ) / 2 ^ b‖ ≤ 1
    rw [← hgU u x, norm_div, norm_pow, Complex.norm_two, div_le_one hP]; exact hdiscI u hu x
  have hv1 : ∀ x, ‖v' x‖ ≤ 1 := fun x => by
    show ‖(v x : ℂ) / 2 ^ b‖ ≤ 1
    rw [← hgU v x, norm_div, norm_pow, Complex.norm_two, div_le_one hP]; exact hdiscI v hv x
  obtain ⟨hUa1, hUa2⟩ := hfwd U (hdiscI u hu)
  obtain ⟨hVa1, hVa2⟩ := hfwd V (hdiscI v hv)
  have hUe : ∀ k, ‖gC (fwdZ p α s t Ft U k) - 2 ^ p * R u' k‖ ≤ E := fun k => by
    have := hUa2 k; simp only [U, hgU u] at this; exact this
  have hVe : ∀ k, ‖gC (fwdZ p α s t Ft V k) - 2 ^ p * R v' k‖ ≤ E := fun k => by
    have := hVa2 k; simp only [V, hgU v] at this; exact this
  -- pointwise product and conjugation
  set Wz : (Fin d → ℕ) → ℤ × ℤ := fun x =>
    conjZ (mulZ p (fwdZ p α s t Ft U x) (fwdZ p α s t Ft V x))
  set y : (Fin d → ℕ) → ℂ := fun x => (starRingEnd ℂ) (R u' x * R v' x)
  have hW1 : InDisc p Wz := fun x => by
    simp only [Wz]; rw [gC_conjZ, Complex.norm_conj]; exact mulZ_disc p _ _ (hUa1 x) (hVa1 x)
  have hW2 : ∀ x, ‖gC (Wz x) / 2 ^ p - y x‖ ≤ (2 * E + Real.sqrt 2) / 2 ^ p := by
    intro x
    have h := mulZ_err p (fwdZ p α s t Ft U x) (fwdZ p α s t Ft V x) (R u' x) (R v' x) (hUa1 x)
      (lip_bound R hRlip hR0 v' hv1 x)
    rw [← conj_err] at h
    rw [show gC (Wz x) / 2 ^ p - y x = (gC (Wz x) - 2 ^ p * y x) / 2 ^ p by field_simp,
      norm_div, norm_pow, Complex.norm_two]
    apply div_le_div_of_nonneg_right _ hP.le
    calc _ ≤ _ := h
      _ ≤ E + E + Real.sqrt 2 := by gcongr; exacts [hUe x, hVe x]
      _ = _ := by ring
  obtain ⟨-, hYa⟩ := hfwd Wz hW1
  have hYe : ∀ k, ‖gC (fwdZ p α s t Ft Wz k) - 2 ^ p * R y k‖ ≤ 3 * E + Real.sqrt 2 := by
    intro k
    have h1 := hYa k
    have h2 := hRlip _ y _ hW2 k
    rw [show gC (fwdZ p α s t Ft Wz k) - 2 ^ p * R y k =
      (gC (fwdZ p α s t Ft Wz k) - 2 ^ p * R (fun i => gC (Wz i) / 2 ^ p) k) +
        2 ^ p * (R (fun i => gC (Wz i) / 2 ^ p) k - R y k) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow, Complex.norm_two]
    calc _ ≤ E + 2 ^ p * ((2 * E + Real.sqrt 2) / 2 ^ p) := by gcongr
      _ = _ := by field_simp; ring
  -- the reference value at in-range indices
  intro j hj
  set c : ℂ := ((2 : ℂ) ^ (2 * α ^ 2))⁻¹
  have hcR : (starRingEnd ℂ) c = c := by simp only [c, map_inv₀, map_pow, map_ofNat]
  set Z := dftBox s (fun m => (starRingEnd ℂ) (dftBox s u' m * dftBox s v' m)) j
  have hRy : R y j = c ^ (3 * d) * Z := by
    rw [hRid y j hj]
    have : dftBox s y j = dftBox s (fun m => (c ^ (2 * d)) *
        (starRingEnd ℂ) (dftBox s u' m * dftBox s v' m)) j := by
      apply dftBox_congr
      intro m hm
      simp only [y]
      rw [hRid u' m hm, hRid v' m hm]; simp only [map_mul, map_pow, hcR]
      ring
    rw [this, dftBox_smul]; ring
  have hconv : ((convBox s u v j : ℤ) : ℂ) =
      2 ^ (2 * b) * (∏ i, (s i : ℂ)) ^ 2 * (starRingEnd ℂ) Z := by
    rw [mul_assoc, conv_id s (fun i => Nat.pos_of_ne_zero (NeZero.ne (s i))) u' v' j hj]
    unfold convBox; push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    simp only [u', v']; field_simp; ring
  -- the final rounding
  set Y := fwdZ p α s t Ft Wz
  set w := convBox s u v j
  set Sn : ℕ := ∏ i, s i
  have hSn : ((Sn : ℕ) : ℂ) = ∏ i, (s i : ℂ) := by simp [Sn]
  set a : ℤ := (Y j).1 * ((Sn : ℕ) : ℤ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2)
  have hex : exactConv p α b s t Ft u v j = roundDiv a (2 ^ p) := rfl
  rw [hex]
  apply roundDiv_eq a w (2 ^ p) (by positivity)
  have hD : ‖gC (Y j) - 2 ^ p * (c ^ (3 * d) * Z)‖ ≤ 3 * E + Real.sqrt 2 := by
    rw [← hRy]; exact hYe j
  have hcd : c ^ (3 * d) = (((2 : ℝ) ^ (6 * d * α ^ 2))⁻¹ : ℝ) := by
    simp only [c]; push_cast; rw [inv_pow, ← pow_mul]; ring_nf
  have hreD : |((Y j).1 : ℝ) - 2 ^ p * ((2 : ℝ) ^ (6 * d * α ^ 2))⁻¹ * Z.re| ≤ 3 * E + Real.sqrt 2 := by
    refine (le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)).trans hD
    have e : gC (Y j) - 2 ^ p * (c ^ (3 * d) * Z) =
        gC (Y j) - (((2 : ℝ) ^ p * ((2 : ℝ) ^ (6 * d * α ^ 2))⁻¹ : ℝ) : ℂ) * Z := by
      rw [hcd]; push_cast; ring
    rw [e, Complex.sub_re, Complex.re_ofReal_mul]
    simp [gC]
  have hw : (w : ℝ) = 2 ^ (2 * b) * (Sn : ℝ) ^ 2 * Z.re := by
    have := congrArg Complex.re hconv
    rw [← hSn] at this
    simp only [Complex.intCast_re] at this
    rw [this, show (2 : ℂ) ^ (2 * b) * ((Sn : ℕ) : ℂ) ^ 2 = (((2 : ℝ) ^ (2 * b) * (Sn : ℝ) ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul, Complex.conj_re]
  have hE : 0 ≤ 3 * E + Real.sqrt 2 := (norm_nonneg _).trans hD
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hK : (0 : ℝ) ≤ (Sn : ℝ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2) := by positivity
  have halg : ((a - w * ((2 ^ p : ℕ) : ℤ) : ℤ) : ℝ) = ((Sn : ℝ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2)) *
      (((Y j).1 : ℝ) - 2 ^ p * ((2 : ℝ) ^ (6 * d * α ^ 2))⁻¹ * Z.re) := by
    push_cast [a]
    rw [hw, pow_add]
    field_simp
  have hfin : 2 * |((a - w * ((2 ^ p : ℕ) : ℤ) : ℤ) : ℝ)| < ((2 ^ p : ℕ) : ℝ) := by
    rw [halg, abs_mul, abs_of_nonneg hK]
    push_cast
    calc 2 * ((Sn : ℝ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2) *
          |((Y j).1 : ℝ) - 2 ^ p * ((2 : ℝ) ^ (6 * d * α ^ 2))⁻¹ * Z.re|)
        ≤ 2 * ((Sn : ℝ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2) * (3 * E + 2)) := by gcongr; linarith
      _ < 2 ^ p := by
        have : ((∏ i, s i : ℕ) : ℝ) = (Sn : ℝ) := rfl
        rw [this] at hprec; linarith
  exact_mod_cast hfin

end IntMul.HvdH.ExMain

open IntMul.HvdH

theorem solution {d : ℕ} (p α b : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : ∀ i, s i ≤ α ^ 2 * (t i - s i))
    (hp : ∀ i, 100 * (jIter p (s i) (t i) α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p)
    (Ft : ((Fin d → ℕ) → ℤ × ℤ) → ((Fin d → ℕ) → ℤ × ℤ)) (εF : ℝ)
    (hFt : ∀ U : (Fin d → ℕ) → ℤ × ℤ, InDisc p U → ∀ j : Fin d → ℕ, (∀ i, j i < t i) →
      ‖gC (Ft U j)‖ ≤ 2 ^ p ∧
      ‖gC (Ft U j) - 2 ^ p * dftBox t (fun x => gC (U x) / 2 ^ p) j‖ ≤ εF)
    (hb : b ≤ p) (u v : (Fin d → ℕ) → ℤ) (hu : ∀ x, |u x| < 2 ^ b) (hv : ∀ x, |v x| < 2 ^ b)
    (hprec : 2 * (3 * ((∑ _i : Fin d, (6 * sWidth p α + 4 : ℝ)) + εF +
        ∑ i, ((jIter p (s i) (t i) α : ℝ) * (10 * eWidth p α + 12) + 4)) + 2) *
        ((∏ i, s i : ℕ) : ℝ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2) < 2 ^ p) :
    ∀ j : Fin d → ℕ, (∀ i, j i < s i) → exactConv p α b s t Ft u v j = convBox s u v j :=
  IntMul.HvdH.ExMain.exactConv_eq p α b s t hst hcop hα hαp hx hp hpA Ft εF hFt hb u v hu hv hprec
