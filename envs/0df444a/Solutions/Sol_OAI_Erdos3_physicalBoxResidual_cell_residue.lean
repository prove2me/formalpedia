-- Prove2me | solution 1 for OAI.Erdos3.physicalBoxResidual_cell_residue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T04:51:22.444589+00:00
-- url     : https://prove2.me/submissions/4f30edbc-c75d-4b60-9b91-3c5b21411200

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B209

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

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

section

namespace Erdos3

open scoped BigOperators Classical

variable {X T A B : Type*} [Fintype X] [Fintype T] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

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

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerVectorResidue_card (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) [NeZero m] :
    Fintype.card (I → ZMod m) = m ^ Fintype.card I := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

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

section

namespace Erdos3

open scoped Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

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

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.physicalBoxResidual_cell_residue.{u_1, u_2} := @OAI.Erdos3.physicalBoxResidual_cell_residue.{u_1, u_2}
