-- Prove2me | solution 1 for OAI.Erdos3.retained_physical_residual_correlation_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:17:03.304454+00:00
-- url     : https://prove2.me/submissions/1b61df10-c1ba-4efb-8249-99b0f8ecfa11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_box_smooth_pair_correlation_s2
import Theorems.Thm_OAI_Erdos3_physicalBoxResidual_control_of_lengths_s2
import Theorems.Thm_OAI_Erdos3_physicalBox_pair_kernel_grid_error_s2
import Theorems.Thm_OAI_Erdos3_shiftedPairLocationKernel_cap_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_energy_aggregate {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (e : X → ℝ) {E : ℝ}
    (he : ∀ a, finiteCellMean p C (fun x => e x ^ 2) a ≤ E * (finiteCellWeights p C).weight a) :
    p.mean (fun x => e x ^ 2) ≤ E := by
  rw [← finiteCellMean_sum p C]
  calc
    _ ≤ ∑ a, E * (finiteCellWeights p C).weight a := Finset.sum_le_sum (fun a _ => he a)
    _ = E := by rw [← Finset.mul_sum, (finiteCellWeights p C).total, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniform_subtype_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (FiniteProbabilityWeights.uniform Ω).mean (fun z => if P z then f z else 0) =
      (Fintype.card {z // P z} : ℝ) / Fintype.card Ω * (𝔼 z : {z // P z}, f z.val) := by
  classical
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
  have hsum : (∑ z, if P z then f z else 0) = ∑ z : {z // P z}, f z.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hsum, ← Fintype.card_mul_expect (fun z : {z // P z} => f z.val)]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteCellMean_uniform {X A : Type*} [Fintype X] [Nonempty X] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X *
        (𝔼 x : {x // C x = a}, f x.val) :=
  uniform_subtype_mean (fun x => C x = a) f

theorem finiteCellWeights_uniform {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (a : A) :
    (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X := by
  change finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun _ => 1) a = _
  rw [finiteCellMean_uniform]
  by_cases h : Nonempty {x // C x = a}
  · let : Nonempty {x // C x = a} := h
    simp
  · let : IsEmpty {x // C x = a} := not_nonempty_iff.mp h
    simp

theorem finiteCellMean_uniform_weighted {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (𝔼 x : {x // C x = a}, f x.val) := by
  rw [finiteCellWeights_uniform, finiteCellMean_uniform]

theorem finiteCellResidueMean_uniform {X A R : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A] [DecidableEq R]
    (C : X → A) (F : X → R) (e : X → ℝ) (a : A) (r : R) :
    finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (𝔼 x : {x // C x = a}, if F x.val = r then e x.val else 0) := by
  have h : finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r =
      finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun x => if F x = r then e x else 0) a := by
    unfold finiteCellResidueMean finiteCellMean
    apply congrArg (FiniteProbabilityWeights.uniform X).mean
    funext x
    by_cases hc : C x = a <;> by_cases hf : F x = r <;> simp [hc, hf]
  rw [h, finiteCellMean_uniform_weighted]

theorem uniform_cell_residue_bound {X A R : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A] [DecidableEq R]
    (C : X → A) (F : X → R) (e : X → ℝ) (a : A) (r : R) {delta : ℝ}
    (he : |𝔼 x : {x // C x = a}, if F x.val = r then e x.val else 0| ≤ delta) :
    |finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a * delta := by
  rw [finiteCellResidueMean_uniform, abs_mul,
    abs_of_nonneg ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg a)]
  exact mul_le_mul_of_nonneg_left he ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrime_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrime Q p ≤ Q :=
  ((mem_boundedPrimes Q p.val).mp p.property).2

theorem boundedPrime_injective (Q : ℕ) : Function.Injective (boundedPrime Q) := Subtype.val_injective

theorem boundedPrimePower_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrimePower Q p ≤ Q := by
  have hQ : 0 < Q := (boundedPrime_prime Q p).pos.trans_le (boundedPrime_le Q p)
  exact Nat.pow_log_le_self p.val hQ.ne'

theorem boundedPrimePower_pairwise (Q : ℕ) :
    Pairwise (fun p r : BoundedPrime Q => (boundedPrimePower Q p).Coprime (boundedPrimePower Q r)) := by
  intro p r hpr
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (boundedPrime_prime Q p) (boundedPrime_prime Q r)).mpr
    (fun h => hpr (Subtype.ext h))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrimeProduct_captures {Q m : ℕ} (hm : 0 < m) (hmQ : m ≤ Q) :
    m ∣ boundedPrimeProduct Q := by
  have hQ : Q ≠ 0 := (hm.trans_le hmQ).ne'
  have hsub : m.primeFactors ⊆ boundedPrimes Q := by
    intro p hp
    have h := Nat.mem_primeFactors.mp hp
    exact (mem_boundedPrimes Q p).mpr ⟨h.1, (Nat.le_of_dvd hm h.2.1).trans hmQ⟩
  have hpow (p : ℕ) (hp : p ∈ m.primeFactors) :
      p ^ m.factorization p ∣ p ^ Nat.log p Q := by
    have hprime := (Nat.mem_primeFactors.mp hp).1
    apply Nat.pow_dvd_pow
    apply (Nat.le_log_iff_pow_le hprime.one_lt hQ).mpr
    exact (Nat.le_of_dvd hm (Nat.ordProj_dvd m p)).trans hmQ
  have hsmall : m ∣ ∏ p ∈ m.primeFactors, p ^ Nat.log p Q := by
    nth_rw 1 [Nat.prod_primeFactors_pow_factorization hm.ne']
    exact Finset.prod_dvd_prod_of_dvd _ _ hpow
  have hlarge := Finset.prod_dvd_prod_of_subset m.primeFactors (boundedPrimes Q)
    (fun p => p ^ Nat.log p Q) hsub
  have h := hsmall.trans hlarge
  have he : boundedPrimeProduct Q = ∏ p ∈ boundedPrimes Q, p ^ Nat.log p Q :=
    Finset.prod_coe_sort (boundedPrimes Q) (fun p => p ^ Nat.log p Q)
  rwa [he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem translatedIntegerBox_eq_piFinset (lo : I → ℤ) (N : I → ℕ) :
    translatedIntegerBox lo N = Fintype.piFinset (fun i => Finset.Ico (lo i) (lo i + N i)) := by
  ext x
  simp only [mem_translatedIntegerBox, Fintype.mem_piFinset, Finset.mem_Ico]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerVectorResidue_card (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) [NeZero m] :
    Fintype.card (I → ZMod m) = m ^ Fintype.card I := by simp

theorem affinePairModulus_pos {J : Type*} [Fintype J] (t u : J → ℤ) (k : J)
    (hne : u k - t k ≠ 0) : 0 < affinePairModulus t u := by
  apply Int.natAbs_pos.mpr
  apply BohrLattice.Primitive.content_ne_zero
  intro h
  exact hne (congrFun h k)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affineInterval_normalized_cap (D : ℕ) (a lo hi x : ℤ) {L C : ℝ}
    (hL : 0 < L) (hx : x ∈ Finset.Ico lo hi)
    (hlow : |((a + (D : ℤ) * lo : ℤ) : ℝ) / L| ≤ C)
    (hhigh : |((a + (D : ℤ) * hi : ℤ) : ℝ) / L| ≤ C) :
    |((a + (D : ℤ) * x : ℤ) : ℝ) / L| ≤ C := by
  have hx' := Finset.mem_Ico.mp hx
  have hleft : ((a + (D : ℤ) * lo : ℤ) : ℝ) ≤ ((a + (D : ℤ) * x : ℤ) : ℝ) := by
    exact_mod_cast add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hx'.1 (Int.natCast_nonneg D))
  have hright : ((a + (D : ℤ) * x : ℤ) : ℝ) ≤ ((a + (D : ℤ) * hi : ℤ) : ℝ) := by
    exact_mod_cast add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hx'.2.le (Int.natCast_nonneg D))
  exact abs_le.mpr ⟨(abs_le.mp hlow).1.trans (div_le_div_of_nonneg_right hleft hL.le),
    (div_le_div_of_nonneg_right hright hL.le).trans (abs_le.mp hhigh).2⟩

theorem normalized_pair_mesh_bound (x y : ℤ) {L H C δ : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hx : |(x : ℝ) / L| ≤ C) (hy : |(y : ℝ) / L| ≤ C)
    (hmesh : 2 * C * L ^ 2 / H ≤ δ) : ((y - x).natAbs : ℝ) * L / H ≤ δ := by
  have hx' : |(x : ℝ)| ≤ C * L := (div_le_iff₀ hL).mp (by simpa only [abs_div, abs_of_pos hL] using hx)
  have hy' : |(y : ℝ)| ≤ C * L := (div_le_iff₀ hL).mp (by simpa only [abs_div, abs_of_pos hL] using hy)
  have hd : ((y - x).natAbs : ℝ) ≤ 2 * C * L := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    exact (abs_sub _ _).trans (by linarith)
  apply le_trans _ hmesh
  apply (div_le_div_iff_of_pos_right hH).mpr
  nlinarith [mul_le_mul_of_nonneg_right hd hL.le]

theorem retained_affine_pair_geometry {J : Type*} [Fintype J]
    (D Q r : ℕ) (a x y : J → ℤ) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (hgood : ¬ affineParameterBadPair D Q r a x y) :
    affinePairModulus (fun j => a j + (D : ℤ) * x j) (fun j => a j + (D : ℤ) * y j) ≤ Q ∧
      ∃ k : J, (a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) ≠ 0 ∧
        κ ≤ |(((a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) : ℤ) : ℝ) / L| := by
  constructor
  · exact le_of_not_gt (fun h => hgood (Or.inl h))
  · have hnear : ¬ ∀ j, |y j - x j| ≤ (r : ℤ) := fun h => hgood (Or.inr h)
    push Not at hnear
    obtain ⟨k, hk⟩ := hnear
    have hr : ((r + 1 : ℕ) : ℝ) ≤ |((y k - x k : ℤ) : ℝ)| := by
      have h : (r + 1 : ℕ) ≤ |y k - x k| := by omega
      exact_mod_cast h
    have heq : (((a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) : ℤ) : ℝ) =
        (D : ℝ) * ((y k - x k : ℤ) : ℝ) := by push_cast; ring
    have hbound : κ ≤ |(((a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) : ℤ) : ℝ) / L| := by
      rw [heq, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg D), abs_of_pos hL]
      apply (le_div_iff₀ hL).mpr
      exact hgap.trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg D))
    refine ⟨k, ?_, hbound⟩
    intro hz
    rw [hz, Int.cast_zero, zero_div, abs_zero] at hbound
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem periodPrimeCoordinates_card_pow_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) : 2 ^ (periodPrimeCoordinates prime M).card ≤ M := by
  classical
  let A := periodPrimeCoordinates prime M
  have hsub : A.image prime ⊆ M.primeFactors := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime i, (mem_periodPrimeCoordinates prime M i).mp hi, hM.ne'⟩
  have hcard : A.card ≤ M.primeFactors.card := by
    rw [← Finset.card_image_of_injective A hinj]
    exact Finset.card_le_card hsub
  calc
    2 ^ A.card ≤ 2 ^ M.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ = ∏ _p ∈ M.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod' fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

theorem periodPrimeCoordinates_pending_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (M : ℕ) (J : Finset ι)
    (hJ : Disjoint J (periodPrimeCoordinates prime M)) :
    Nat.Coprime (∏ i ∈ J, prime i ^ power i) M := by
  classical
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.Coprime.pow_left
  apply (hprime i).coprime_iff_not_dvd.mpr
  intro hd
  exact Finset.disjoint_left.mp hJ hi ((mem_periodPrimeCoordinates prime M i).mpr hd)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem periodPrimeCoordinates_modulus_dvd_product {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (m : ℕ)
    (hm : m ∣ ∏ i, prime i ^ power i) :
    m ∣ ∏ i ∈ periodPrimeCoordinates prime m, prime i ^ power i := by
  let I := periodPrimeCoordinates prime m
  have hc := (periodPrimeCoordinates_pending_coprime prime power hprime m Iᶜ
    (Finset.disjoint_left.mpr (fun _ hi hI => (Finset.mem_compl.mp hi) hI))).symm
  apply hc.dvd_of_dvd_mul_right
  rw [Finset.prod_mul_prod_compl]
  exact hm

theorem periodPrimeCoordinates_card_le_of_le_pow {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {m b : ℕ} (hm : 0 < m) (hmb : m ≤ 2 ^ b) :
    (periodPrimeCoordinates prime m).card ≤ b := by
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((periodPrimeCoordinates_card_pow_le prime hprime hinj hm).trans hmb)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))

theorem primeCoordinatesMod_agree (m : ℕ) (hd : m ∣ ∏ i : I, q i.val)
    (x y : ∀ i, σ → ZMod (q i)) (hxy : ∀ i ∈ I, x i = y i) :
    primeCoordinatesMod q I hpair m hd x = primeCoordinatesMod q I hpair m hd y := by
  ext k
  change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm (fun i : I => x i.val k)) =
    (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm (fun i : I => y i.val k))
  congr 2
  funext i
  exact congrFun (hxy i.val i.property) k

theorem primeCoordinatesMod_integer (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (u : σ → ℤ) :
    primeCoordinatesMod q I hpair m hd (primeCoordinateObservation q u) = (fun k => (u k : ZMod m)) := by
  ext k
  change (ZMod.castHom hd (ZMod m))
    ((selectedPrimeCRT q I hpair).symm (u k : ∀ i : I, ZMod (q i.val))) = _
  rw [map_intCast, map_intCast]

theorem primeCoordinatesMod_surjective (m : ℕ) [NeZero m] (hd : m ∣ ∏ i : I, q i.val) :
    Function.Surjective (primeCoordinatesMod (σ := σ) q I hpair m hd) := by
  intro y
  refine ⟨primeCoordinateObservation q (fun k => ((y k).val : ℤ)), ?_⟩
  rw [primeCoordinatesMod_integer]
  funext k
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
  (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m)

theorem coarseResidueIndicator_depends :
    ProductDependsOn I (coarseResidueIndicator q I hpair m hd r) := by
  intro x y hxy
  unfold coarseResidueIndicator
  rw [primeCoordinatesMod_agree q I hpair m hd x y hxy]

theorem coarseResidueIndicator_abs (x : ∀ i, σ → ZMod (q i)) :
    |coarseResidueIndicator q I hpair m hd r x| = coarseResidueIndicator q I hpair m hd r x := by
  unfold coarseResidueIndicator
  split_ifs <;> norm_num

theorem coarseResidueIndicator_integer (u : σ → ℤ) :
    coarseResidueIndicator q I hpair m hd r (primeCoordinateObservation q u) =
      if (fun k => (u k : ZMod m)) = r then (1 : ℝ) else 0 := by
  simp only [coarseResidueIndicator, primeCoordinatesMod_integer]

end

theorem primeCoordinateReference_uniform {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)] :
    FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q) =
      FiniteProbabilityWeights.uniform (∀ i, σ → ZMod (q i)) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  change (∏ i, (Fintype.card (σ → ZMod (q i)) : ℝ)⁻¹) =
    (Fintype.card (∀ i, σ → ZMod (q i)) : ℝ)⁻¹
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

theorem coarseResidueIndicator_mean {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι)
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) [NeZero m] (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m) :
    (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).mean
      (coarseResidueIndicator q I hpair m hd r) = ((m : ℝ) ^ Fintype.card σ)⁻¹ := by
  rw [primeCoordinateReference_uniform]
  have h := uniform_mean_surjective_hom_fiber (primeCoordinatesMod (σ := σ) q I hpair m hd)
    (primeCoordinatesMod_surjective q I hpair m hd) r
  convert h using 1
  · congr 1
  · simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePhysicalTruncation_modulus_error {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    {b : ℕ} {f : (σ → ℤ) → ℝ} {eta : ℝ}
    (h : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (I : Finset ι) (hI : I.card ≤ b) (m : ℕ) [NeZero m]
    (hd : m ∣ ∏ i ∈ I, q i) (r : σ → ZMod m) :
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (z k).val)) *
        (if (fun k => ((z k).val : ZMod m)) = r then (1 : ℝ) else 0)| ≤
      eta * residueTruncationCap ι b eta * ((m : ℝ) ^ Fintype.card σ)⁻¹ := by
  have hd' : m ∣ ∏ i : I, q i.val := by simpa only [Finset.prod_coe_sort] using hd
  have ht := h.2.2 I hI (coarseResidueIndicator q I hpair m hd' r)
    (coarseResidueIndicator_depends q I hpair m hd' r)
  simp_rw [coarseResidueIndicator_integer, coarseResidueIndicator_abs] at ht
  rw [coarseResidueIndicator_mean] at ht
  convert ht using 1
  congr 3
  funext z
  split_ifs <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCellResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem physical_cell_residual_energy {X A ι σ : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (C : X → A) (c : A) (e : X → ℝ)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ)
    (hcontrol : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (E : {x // C x = c} ≃ IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
    (he : ∀ x : {x // C x = c}, e x.val =
      f (fun k => (E x k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (E x k).val)) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun x => e x ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) * (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight c := by
  have hmean := Fintype.expect_equiv E (fun x => e x.val ^ 2)
    (fun z => (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f
      (fun k => (z k).val)) ^ 2) (fun x => by rw [he x])
  rw [finiteCellMean_uniform_weighted, hmean]
  exact (mul_le_mul_of_nonneg_left hcontrol.2.1
    ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg c)).trans_eq (mul_comm _ _)

theorem physical_cell_residual_residue {X A ι σ : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (C : X → A) (c : A) (e : X → ℝ)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ)
    (hcontrol : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (E : {x // C x = c} ≃ IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
    (he : ∀ x : {x // C x = c}, e x.val =
      f (fun k => (E x k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (E x k).val))
    (J : Finset ι) (hJ : J.card ≤ b) (m : ℕ) [NeZero m] (hm : m ∣ ∏ i ∈ J, q i)
    (F : X → σ → ZMod m) (hF : ∀ x : {x // C x = c},
      F x.val = integerVectorResidue m (fun k => (E x k).val)) (r : σ → ZMod m) :
    |finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight c *
        (eta * residueTruncationCap ι b eta / Fintype.card (σ → ZMod m)) := by
  classical
  apply uniform_cell_residue_bound
  have hmean := Fintype.expect_equiv E (fun x => if F x.val = r then e x.val else 0)
    (fun z => (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f
      (fun k => (z k).val)) * (if (fun k => ((z k).val : ZMod m)) = r then (1 : ℝ) else 0))
    (fun x => by
      rw [he x, hF x]
      change (if (fun k => ((E x k).val : ZMod m)) = r then _ else 0) = _
      split_ifs <;> simp)
  rw [hmean]
  have h := residuePhysicalTruncation_modulus_error lo N M a hne q hpair hcontrol J hJ m hm r
  simpa only [integerVectorResidue_card, Nat.cast_pow, div_eq_mul_inv] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPair_pivot_card (k : J) : Fintype.card {j : J // j ≠ k} = Fintype.card J - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem smoothPairRowLipschitz_pivot (k l : J) : smoothPairRowLipschitz k = smoothPairRowLipschitz l := by
  simp only [smoothPairRowLipschitz, smoothPair_pivot_card]

theorem smoothPairProbabilityError_pivot (k l : J) (Q : ℕ) (C κ δ : ℝ) :
    smoothPairProbabilityError k Q C κ δ = smoothPairProbabilityError l Q C κ δ := by
  simp only [smoothPairProbabilityError, smoothPair_pivot_card, smoothPairRowLipschitz_pivot k l]

theorem smoothPairProbabilityCap_pivot (k l : J) (Q : ℕ) (C κ : ℝ) :
    smoothPairProbabilityCap k Q C κ = smoothPairProbabilityCap l Q C κ := by
  simp only [smoothPairProbabilityCap, smoothPair_pivot_card]

theorem fullSmoothPairError_pivot (n : ℕ) (k l : J) (Q : ℕ) (C κ δ : ℝ) :
    fullSmoothPairError n k Q C κ δ = fullSmoothPairError n l Q C κ δ := by
  simp only [fullSmoothPairError, smoothPairProbabilityCap_pivot k l, smoothPairProbabilityError_pivot k l]

theorem smoothPairKernelCap_pivot (n : ℕ) (k l : J) (C κ : ℝ) :
    smoothPairKernelCap n k C κ = smoothPairKernelCap n l C κ := by
  simp only [smoothPairKernelCap, smoothPairKernelBaseCap, smoothPair_pivot_card]

theorem smoothPairKernelLip_pivot (n : ℕ) (k l : J) (C κ : ℝ) :
    smoothPairKernelLip n k C κ = smoothPairKernelLip n l C κ := by
  simp only [smoothPairKernelLip, smoothPairKernelCap_pivot n k l, smoothPairKernelBaseLip,
    smoothPair_pivot_card, smoothPairRowLipschitz_pivot k l]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxResidual_zero_off (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (hx : x ∉ translatedIntegerBox lo N) :
    physicalBoxResidual lo N P hpos q b f x = 0 := by
  simp only [physicalBoxResidual, if_neg hx]

theorem physicalBoxResidual_on_cell (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (c : ∀ i, (P i).Label) (x : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c}) :
    physicalBoxResidual lo N P hpos q b f x.val.val = f x.val.val -
      residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x.val.val := by
  simp only [physicalBoxResidual, if_pos x.val.property,
    physicalBoxTruncation, dif_pos x.val.property]
  rw [x.property]

theorem physicalBoxResidual_cell_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ) (c : ∀ i, (P i).Label)
    (hc : ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    finiteCellMean (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) *
        (finiteCellWeights (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)).weight c := by
  exact physical_cell_residual_energy (physicalBoxCell lo N P) c
    (fun x => physicalBoxResidual lo N P hpos q b f x.val) _ _ 1 (fun _ => 0)
    (physicalBoxCell_nonempty lo N P hpos c) q b f eta hc (physicalBoxCellEquiv lo N P hstep hpos c)
    (physicalBoxResidual_on_cell lo N P hpos q b f c)

theorem physicalBoxResidual_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ)
    (hc : ∀ c : (∀ i, (P i).Label), ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)).mean
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) ≤
      1 + eta * residueTruncationCap ι b eta ^ 2 := by
  exact finite_cell_energy_aggregate (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N))
    (physicalBoxCell lo N P) (fun x => physicalBoxResidual lo N P hpos q b f x.val)
    (fun c => physicalBoxResidual_cell_energy lo N P hstep hpos q b f eta c (hc c))

theorem physicalBoxResidual_cell_residue (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ) (c : ∀ i, (P i).Label)
    (hc : ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta)
    (J : Finset ι) (hJ : J.card ≤ b) (m : ℕ) [NeZero m] (hm : m ∣ ∏ j ∈ J, q j) (r : I → ZMod m) :
    |finiteCellResidueMean (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)
      (fun x => integerVectorResidue m x.val) (fun x => physicalBoxResidual lo N P hpos q b f x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)).weight c *
        (eta * residueTruncationCap ι b eta / (m : ℝ) ^ Fintype.card I) := by
  have h := physical_cell_residual_residue (physicalBoxCell lo N P) c
    (fun x => physicalBoxResidual lo N P hpos q b f x.val) _ _ 1 (fun _ => 0)
    (physicalBoxCell_nonempty lo N P hpos c) q hpair b f eta hc (physicalBoxCellEquiv lo N P hstep hpos c)
    (physicalBoxResidual_on_cell lo N P hpos q b f c) J hJ m hm
    (fun x => integerVectorResidue m x.val) (fun _ => rfl) r
  simpa only [integerVectorResidue_card, Nat.cast_pow] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueTruncationCap_nonneg (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) {eta : ℝ} (heta : 0 ≤ eta) : 0 ≤ residueTruncationCap ι b eta := by
  unfold residueTruncationCap
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalResidualCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem physical_box_residual_correlation {J I ι : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) [Nonempty (translatedIntegerBox lo N)]
    (hside : ∀ i, (affinePairModulus t u : ℝ) ≤ (N i : ℝ))
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (degree : ℕ) (f g : (I → ℤ) → ℝ) (eta ρ : ℝ) (heta : 0 ≤ eta) (hρ : 0 ≤ ρ)
    (hgrid : ∀ i c, ((P i).length c : ℝ) ≤ ρ * H i)
    (hcf : ∀ c : (∀ i, (P i).Label),
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree f eta)
    (hcg : ∀ c : (∀ i, (P i).Label),
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree g eta)
    (S : Finset ι) (hS : S.card ≤ degree) (hm : affinePairModulus t u ∣ ∏ j ∈ S, q j) :
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos q degree f (smoothAffineSample t z.val) *
        physicalBoxResidual lo N P hpos q degree g (smoothAffineSample u z.val))| ≤
      ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
        ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap ι degree eta) ^ 2 +
          (fullSmoothPairError (Fintype.card I) k Q C κ δ +
            (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
              (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap ι degree eta ^ 2)) := by
  let : NeZero (affinePairModulus t u) := ⟨(affinePairModulus_pos t u k hne).ne'⟩
  let e : (I → ℤ) → ℝ := physicalBoxResidual lo N P hpos q degree f
  let d : (I → ℤ) → ℝ := physicalBoxResidual lo N P hpos q degree g
  let cell : (∀ i, (P i).Label) → (∀ i, (P i).Label) → (I → ZMod (affinePairModulus t u)) → ℝ :=
    fun c c' _ => shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) origin
      (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => intervalCellLower (lo i) (P i) (c' i))
  have hlen (i : I) : lo i < lo i + (N i : ℤ) := by
    have hmpos : (0 : ℝ) < affinePairModulus t u := by exact_mod_cast affinePairModulus_pos t u k hne
    have hN : 0 < N i := by exact_mod_cast hmpos.trans_le (hside i)
    exact lt_add_of_pos_right _ (by exact_mod_cast hN)
  have hw (i : I) : (affinePairModulus t u : ℝ) ≤ ((lo i + N i - lo i : ℤ) : ℝ) := by
    simpa only [add_sub_cancel_left, Int.cast_natCast] using hside i
  have hbound := box_smooth_pair_correlation_s2
    (alpha := eta * residueTruncationCap ι degree eta) (beta := eta * residueTruncationCap ι degree eta)
    t u k hne H Q hH hL hC hκ hδ hδ1
    ht hu hgap hQ hmesh hsmall origin hZ lo (fun i => lo i + N i) lo (fun i => lo i + N i)
    hlen hlen hw hw (translatedIntegerBox lo N) (translatedIntegerBox lo N)
    (translatedIntegerBox_eq_piFinset lo N) (translatedIntegerBox_eq_piFinset lo N)
    e d (physicalBoxResidual_zero_off lo N P hpos q degree f)
    (physicalBoxResidual_zero_off lo N P hpos q degree g)
    (physicalBoxCell lo N P) (physicalBoxCell lo N P) cell
    (mul_nonneg heta (residueTruncationCap_nonneg ι degree heta))
    (smoothPairKernelCap (Fintype.card I) k C κ).coe_nonneg
    (mul_nonneg (smoothPairKernelLip (Fintype.card I) k C κ).coe_nonneg hρ)
    (fun c r => by
      simpa only [mul_div_assoc] using
        physicalBoxResidual_cell_residue lo N P hstep hpos q hpair degree f eta c (hcf c) S hS _ hm r)
    (fun c r => by
      simpa only [mul_div_assoc] using
        physicalBoxResidual_cell_residue lo N P hstep hpos q hpair degree g eta c (hcg c) S hS _ hm r)
    (fun c c' _ => shiftedPairLocationKernel_cap_s2 t u k hne H L hH (zero_lt_one.trans_le hL)
      hC hκ (ht k) (hu k) hgap origin _ _)
    (fun x y _ => physicalBox_pair_kernel_grid_error_s2 t u k hne H L hH (zero_lt_one.trans_le hL)
      hC hκ hρ (ht k) (hu k) hgap origin lo N P hstep hgrid x y)
  have he := physicalBoxResidual_energy lo N P hstep hpos q degree f eta hcf
  have hd := physicalBoxResidual_energy lo N P hstep hpos q degree g eta hcg
  have herr : 0 ≤ fullSmoothPairError (Fintype.card I) k Q C κ δ +
      (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ :=
    add_nonneg (fullSmoothPairError_nonneg _ k Q C κ δ hδ)
      (mul_nonneg (NNReal.coe_nonneg _) hρ)
  apply hbound.trans
  calc
    _ ≤ ((translatedIntegerBox lo N).card : ℝ) * (translatedIntegerBox lo N).card / (∏ i, H i ^ 2) *
      ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap ι degree eta) *
        (eta * residueTruncationCap ι degree eta) +
       (fullSmoothPairError (Fintype.card I) k Q C κ δ +
          (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
        ((2 : ℝ) ^ Fintype.card I / 2 * ((1 + eta * residueTruncationCap ι degree eta ^ 2) +
          (1 + eta * residueTruncationCap ι degree eta ^ 2)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ herr
      exact mul_le_mul_of_nonneg_left (add_le_add he hd) (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedBoxPartitions_step {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    (normalizedBoxPartitions N H ρ hlarge hwhole i).step c = 1 := rfl

theorem normalizedBoxPartitions_lengths {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    ρ * H i / 4 ≤ ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ∧
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ≤ ρ * H i := by
  obtain ⟨_, _, hlo, hup⟩ := normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)
  have hl := comparableBoxPartitions_length N (fun j => ⌊ρ * H j / 2⌋₊)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).1)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).2.1) i c
  have hl' : (⌊ρ * H i / 2⌋₊ : ℝ) ≤
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) := by exact_mod_cast hl.1
  have hu' : ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) <
      2 * (⌊ρ * H i / 2⌋₊ : ℝ) := by exact_mod_cast hl.2
  exact ⟨hlo.trans hl', by linarith⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalized_physical_residual_correlation {J I ι : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (q : ι → ℕ) [∀ j, NeZero (q j)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hmoduli : ∀ j, (q j : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (S : Finset ι) (hS : S.card ≤ degree) (hm : affinePairModulus t u ∣ ∏ j ∈ S, q j) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos q degree f (smoothAffineSample t z.val) *
        physicalBoxResidual lo N P hpos q degree g (smoothAffineSample u z.val))| ≤
      ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
        ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap ι degree eta) ^ 2 +
          (fullSmoothPairError (Fintype.card I) k Q C κ δ +
            (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
              (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap ι degree eta ^ 2)) := by
  let P : ∀ i, FiniteProgressionPartition (N i) := normalizedBoxPartitions N H ρ hlarge hwhole
  let hpos : ∀ i c, 0 < (P i).length c := normalizedBoxPartitions_positive N H ρ hlarge hwhole
  have hstep : ∀ i c, (P i).step c = 1 := normalizedBoxPartitions_step N H ρ hlarge hwhole
  have hN (i : I) : 0 < N i := by
    have hr : (0 : ℝ) < N i := by linarith [hlarge i, hwhole i]
    exact_mod_cast hr
  let : Nonempty (translatedIntegerBox lo N) := ⟨⟨lo, (mem_translatedIntegerBox lo N lo).mpr
    (fun i => ⟨le_rfl, lt_add_of_pos_right _ (by exact_mod_cast hN i)⟩)⟩⟩
  have hwidth (i : I) : (affinePairModulus t u : ℝ) ≤ (N i : ℝ) :=
    (by exact_mod_cast hQ : (affinePairModulus t u : ℝ) ≤ Q).trans (hside i)
  have hlength' (i : I) (c : (P i).Label) :
      Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ((P i).length c : ℝ) :=
    (hlength i).trans (normalizedBoxPartitions_lengths N H ρ hlarge hwhole i c).1
  have hcf (c : ∀ i, (P i).Label) :
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree f eta :=
    physicalBoxResidual_control_of_lengths_s2 lo N P hstep hpos q hpair degree f hf
      modLog dimLog accLog eta hmodLog heta hacc hmoduli hdim hlength' c
  have hcg (c : ∀ i, (P i).Label) :
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree g eta :=
    physicalBoxResidual_control_of_lengths_s2 lo N P hstep hpos q hpair degree g hg
      modLog dimLog accLog eta hmodLog heta hacc hmoduli hdim hlength' c
  exact physical_box_residual_correlation t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap hQ hmesh hsmall
    origin hZ lo N hwidth P hstep hpos q hpair degree f g eta ρ ((Real.exp_pos _).le.trans hacc) hρ
    (fun i c => (normalizedBoxPartitions_lengths N H ρ hlarge hwhole i c).2) hcf hcg S hS hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem boundedPrime_small_support (Q degree m : ℕ) (hm : 0 < m) (hmQ : m ≤ Q) (hQdegree : Q ≤ 2 ^ degree) :
    ∃ S : Finset (BoundedPrime Q), S.card ≤ degree ∧ m ∣ ∏ j ∈ S, boundedPrimePower Q j := by
  refine ⟨periodPrimeCoordinates (boundedPrime Q) m, ?_, ?_⟩
  · exact periodPrimeCoordinates_card_le_of_le_pow (boundedPrime Q) (boundedPrime_prime Q)
      (boundedPrime_injective Q) hm (hmQ.trans hQdegree)
  · exact periodPrimeCoordinates_modulus_dvd_product (boundedPrime Q) (boundedPrimeExponent Q)
      (boundedPrime_prime Q) m (boundedPrimeProduct_captures hm hmQ)

theorem bounded_prime_physical_residual_correlation {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f (smoothAffineSample t z.val) *
        physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree g (smoothAffineSample u z.val))| ≤
      ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
        ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap (BoundedPrime Q) degree eta) ^ 2 +
          (fullSmoothPairError (Fintype.card I) k Q C κ δ +
            (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
              (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2)) := by
  obtain ⟨S, hS, hm⟩ := boundedPrime_small_support Q degree (affinePairModulus t u)
    (affinePairModulus_pos t u k hne) hQ hQdegree
  exact normalized_physical_residual_correlation t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap hQ
    hmesh hsmall origin hZ lo N hside (boundedPrimePower Q) (boundedPrimePower_pairwise Q) degree f g hf hg
    eta ρ modLog dimLog accLog hρ heta hmodLog hacc
    (fun j => (Nat.cast_le.mpr (boundedPrimePower_le Q j)).trans hQlog) hdim hlarge hwhole hlength S hS hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_physical_residual_correlation {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (t u : J → ℤ) (k0 : J)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : ∃ k : J, u k - t k ≠ 0 ∧ κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, 2 * C * L ^ 2 / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k0}) * smoothPairRowLipschitz k0 * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f (smoothAffineSample t z.val) *
        physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree g (smoothAffineSample u z.val))| ≤
      physicalResidualPairBudget lo N H k0 Q C κ δ degree eta ρ := by
  obtain ⟨k, hne, hk⟩ := hgap
  have hsmallk : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2 := by
    simpa only [smoothPair_pivot_card, smoothPairRowLipschitz_pivot k k0] using hsmall
  have h := bounded_prime_physical_residual_correlation t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hk hQ
    (fun i => normalized_pair_mesh_bound (t k) (u k) (zero_lt_one.trans_le hL) (hH i) (ht k) (hu k) (hmesh i))
    hsmallk origin hZ lo N hside degree f g hf hg eta ρ modLog dimLog accLog hρ heta hmodLog hacc hQlog hdim
    hlarge hwhole hlength hQdegree
  simpa only [physicalResidualPairBudget, smoothPairKernelCap_pivot (Fintype.card I) k k0,
    smoothPairKernelLip_pivot (Fintype.card I) k k0, fullSmoothPairError_pivot (Fintype.card I) k k0] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem retained_physical_residual_correlation_s2_oai {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ)
    (x y : ∀ j, Finset.Ico (parLo j) (parHi j))
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (hgood : ¬ affineParameterBadPair D Q r anchor (fun j => (x j).val) (fun j => (y j).val))
    (hmesh : ∀ i, 2 * C * L ^ 2 / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k0}) * smoothPairRowLipschitz k0 * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f (smoothAffineSample (fun j => anchor j + (D : ℤ) * (x j).val) z.val) *
        physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree g (smoothAffineSample (fun j => anchor j + (D : ℤ) * (y j).val) z.val))| ≤
      physicalResidualPairBudget lo N H k0 Q C κ δ degree eta ρ := by
  obtain ⟨hQ, hpivot⟩ := retained_affine_pair_geometry D Q r anchor (fun j => (x j).val) (fun j => (y j).val)
    (zero_lt_one.trans_le hL) hκ hgap hgood
  exact uniform_physical_residual_correlation
    (fun j => anchor j + (D : ℤ) * (x j).val) (fun j => anchor j + (D : ℤ) * (y j).val)
    k0 H Q hH hL hC hκ hδ hδ1
    (fun j => affineInterval_normalized_cap D (anchor j) (parLo j) (parHi j) (x j).val
      (zero_lt_one.trans_le hL) (x j).property (hleft j) (hright j))
    (fun j => affineInterval_normalized_cap D (anchor j) (parLo j) (parHi j) (y j).val
      (zero_lt_one.trans_le hL) (y j).property (hleft j) (hright j))
    hpivot hQ hmesh hsmall origin hZ lo N hside degree f g hf hg eta ρ modLog dimLog accLog hρ heta hmodLog
    hacc hQlog hdim hlarge hwhole hlength hQdegree

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.retained_physical_residual_correlation_s2_oai.{u_1, u_2} := @OAI.Erdos3.retained_physical_residual_correlation_s2_oai.{u_1, u_2}
