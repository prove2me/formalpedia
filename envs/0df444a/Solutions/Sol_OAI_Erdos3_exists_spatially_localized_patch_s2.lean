-- Prove2me | solution 1 for OAI.Erdos3.exists_spatially_localized_patch_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:46:22.072709+00:00
-- url     : https://prove2.me/submissions/4ac5f756-81ed-478e-ac9d-3eef2e5e0fce

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B302
import Theorems.Thm_OAI_Erdos3_exists_torusCell_affine_recovery_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3.TriangularSlots

variable {D E : ℕ}

theorem factorized_patchValue_at_lift
    (A : TriangularSlots D) (B : (Fin D → ℤ) → TriangularSlots E)
    (T : TriangularSlots (D + E)) (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (K : PatchKernel (D + E)) (I : SlotInterleaving D E)
    (hterm : ∀ z, K.value (T.residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value ((B (fun j => z (I.left j))).residual (fun j => z (I.right j))))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3) :
    T.patchValue K = Φ.value (A.residual b) * (B b).patchValue Ψ := by
  have hleft (z : Fin (D + E) → ℤ)
      (hz : Φ.value (A.residual (fun j => z (I.left j))) ≠ 0) :
      (fun j => z (I.left j)) = b :=
    A.integer_unique (by norm_num) (Φ.support _ hz) hb
  by_cases hφ : Φ.value (A.residual b) = 0
  · rw [hφ, zero_mul]
    apply T.patchValue_eq_zero K
    intro z
    rw [hterm]
    by_cases hz : Φ.value (A.residual (fun j => z (I.left j))) = 0
    · rw [hz, zero_mul]
    · rw [hleft z hz, hφ, zero_mul]
  · by_cases hc : ∃ c, Ψ.value ((B b).residual c) ≠ 0
    · obtain ⟨c, hc⟩ := hc
      have hz : K.value (T.residual (I.fill b c)) ≠ 0 := by
        simpa only [hterm, SlotInterleaving.fill_left, SlotInterleaving.fill_right] using
          mul_ne_zero hφ hc
      rw [T.patchValue_eq_of_nonzero K hz, (B b).patchValue_eq_of_nonzero Ψ hc, hterm]
      simp only [SlotInterleaving.fill_left, SlotInterleaving.fill_right]
    · have hc : ∀ c, Ψ.value ((B b).residual c) = 0 := by simpa using hc
      rw [(B b).patchValue_eq_zero Ψ hc, mul_zero]
      apply T.patchValue_eq_zero K
      intro z
      rw [hterm]
      by_cases hz : Φ.value (A.residual (fun j => z (I.left j))) = 0
      · rw [hz, zero_mul]
      · rw [hleft z hz, hc, mul_zero]

theorem factorized_patchValue
    (A : TriangularSlots D) (B : (Fin D → ℤ) → TriangularSlots E)
    (T : TriangularSlots (D + E)) (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (K : PatchKernel (D + E)) (I : SlotInterleaving D E)
    (hterm : ∀ z, K.value (T.residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value ((B (fun j => z (I.left j))).residual (fun j => z (I.right j)))) :
    T.patchValue K = ∑' b, Φ.value (A.residual b) * (B b).patchValue Ψ := by
  classical
  by_cases h : ∃ b, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    rw [A.factorized_patchValue_at_lift B T Φ Ψ K I hterm b
      (fun i => (Φ.support _ hb i).trans (by norm_num))]
    symm
    apply tsum_eq_single b
    intro c hcb
    have hc : Φ.value (A.residual c) = 0 := by
      by_contra hc
      exact hcb (A.contributing_unique Φ hc hb)
    rw [hc, zero_mul]
  · have hzero : ∀ b, Φ.value (A.residual b) = 0 := by simpa using h
    rw [T.patchValue_eq_zero K (fun z => by rw [hterm, hzero, zero_mul])]
    simp only [hzero, zero_mul, tsum_zero]

end Erdos3.TriangularSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FlatPatchReset
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

namespace PatchKernel

variable {d : ℕ} (Φ : PatchKernel d)

theorem periodicValue_integer_periodic (x : Fin d → ℝ) (m : Fin d → ℤ) :
    Φ.periodicValue (fun i => x i + m i) = Φ.periodicValue x := by
  change (∑' b : Fin d → ℤ, Φ.value (fun i => (b i : ℝ) - (x i + m i))) =
    ∑' b : Fin d → ℤ, Φ.value (fun i => (b i : ℝ) - x i)
  have heq := (Equiv.addRight m).tsum_eq
    (fun b : Fin d → ℤ => Φ.value (fun i => (b i : ℝ) - (x i + m i)))
  refine heq.symm.trans (tsum_congr fun b => ?_)
  congr 1
  funext i
  change ((b i + m i : ℤ) : ℝ) - (x i + m i) = (b i : ℝ) - x i
  push_cast
  ring

end PatchKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem ofCoordinates_center (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (t : σ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    ((ofCoordinates P hP).slots t).center x i = aeval t (P i) := by
  simp only [slots, ofCoordinates, MvPolynomial.comp_aeval_apply, aeval_X, Sum.elim_inl]

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

theorem placeCenter_eval {w : Fin d → ℕ} (A : PolynomialSlots σ d w)
    (f : Fin d → Fin n) (hf : StrictMono f) (i : Fin d) (t : σ → ℝ) (x : Fin n → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (f i) j))) (A.placeCenter f (f i) i) =
      (A.slots t).center (fun j => x (f j)) i := by
  simp only [placeCenter, MvPolynomial.comp_aeval_apply, slots]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a => simp [placementSubstitution]
  | inr j =>
    have h : (f (earlierSlot i j)).val < (f i).val :=
      hf (show earlierSlot i j < i from j.isLt)
    simp only [placementSubstitution, Sum.elim_inr, dif_pos h, aeval_X]
    rfl

end PolynomialSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem aeval_eq_of_weightedSupport {σ R : Type*} [CommRing R]
    {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (x y : σ → R)
    (hxy : ∀ i, w i ≤ d → x i = y i) : aeval x p = aeval y p := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun z => z ^ α i)
    (hxy i ((Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hi)).trans (hp hα)))

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace SlotInterleaving

theorem sorted_left_lt_right {D E : ℕ} (w : Fin D → ℕ) (v : Fin E → ℕ)
    (hw : Monotone w) (hv : Monotone v) (i : Fin D) (j : Fin E) (h : w i ≤ v j) :
    (sorted w v hw hv).left i < (sorted w v hw hv).right j := by
  apply stable_sort_symm_lt (Fin.append w v)
  · simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · simpa only [Fin.append_left, Fin.append_right] using h

end SlotInterleaving

namespace WeightedParameterSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

theorem insertCenter_eval
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (i : Fin E) (t : σ → ℝ) (x : Fin (D + E) → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (I.right i) j)))
        (B.insertCenter I (I.right i) i) =
      (B.slots (Sum.elim t (fun j => x (I.left j)))).center (fun j => x (I.right j)) i := by
  simp only [insertCenter, MvPolynomial.comp_aeval_apply, slots]
  apply aeval_eq_of_weightedSupport (B.degree i)
  intro a ha
  rcases a with (a | j) | j
  · simp [insertSubstitution]
  · have h : (I.left j).val < (I.right i).val := hbefore j i ha
    simp only [insertSubstitution, Sum.elim_inl, Sum.elim_inr, dif_pos h, aeval_X]
    rfl
  · have h : (I.right (earlierSlot i j)).val < (I.right i).val :=
      I.right_strictMono j.isLt
    simp only [insertSubstitution, Sum.elim_inr, PolynomialSlots.placementSubstitution,
      dif_pos h, aeval_X]
    rfl

end WeightedParameterSlots

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

theorem insertLifts_center_left (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (t : σ → ℝ) (x : Fin (D + E) → ℝ) (i : Fin D) :
    ((A.insertLifts B I).slots t).center x (I.left i) =
      (A.slots t).center (fun j => x (I.left j)) i := by
  change aeval _ (Fin.addCases _ _ (I.perm (I.left i))) = _
  rw [show I.perm (I.left i) = i.castAdd E from I.perm.apply_symm_apply _, Fin.addCases_left]
  exact A.placeCenter_eval I.left I.left_strictMono i t x

theorem insertLifts_center_right (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (t : σ → ℝ) (x : Fin (D + E) → ℝ) (i : Fin E) :
    ((A.insertLifts B I).slots t).center x (I.right i) =
      (B.slots (Sum.elim t (fun j => x (I.left j)))).center (fun j => x (I.right j)) i := by
  change aeval _ (Fin.addCases _ _ (I.perm (I.right i))) = _
  rw [show I.perm (I.right i) = i.natAdd D from I.perm.apply_symm_apply _, Fin.addCases_right]
  exact B.insertCenter_eval I hbefore i t x

theorem insertLifts_residual_left (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (t : σ → ℝ) (z : Fin (D + E) → ℤ) (i : Fin D) :
    ((A.insertLifts B I).slots t).residual z (I.left i) =
      (A.slots t).residual (fun j => z (I.left j)) i := by
  simp only [TriangularSlots.residual, insertLifts_center_left]

theorem insertLifts_residual_right (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (t : σ → ℝ) (z : Fin (D + E) → ℤ) (i : Fin E) :
    ((A.insertLifts B I).slots t).residual z (I.right i) =
      (B.slots (Sum.elim t (fun j => (z (I.left j) : ℝ)))).residual
        (fun j => z (I.right j)) i := by
  simp only [TriangularSlots.residual, insertLifts_center_right A B I hbefore]

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {d : ℕ} {w : Fin d → ℕ}

theorem reparam_slots (A : WeightedParameterSlots σ p d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (t : τ → ℝ) :
    (A.reparam f hf).slots t = A.slots (fun a => aeval t (f a)) := by
  apply TriangularSlots.ext
  intro x i
  simp only [slots, reparam, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a =>
    simp only [parameterSubstitution, Sum.elim_inl, MvPolynomial.comp_aeval_apply, aeval_X]
  | inr j => simp [parameterSubstitution]

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {s d : ℕ}

theorem reparam_value (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (t : τ → ℝ) :
    (A.reparam f hf).value t = A.value (fun a => aeval t (f a)) := by
  change ((A.form.reparam f hf).slots t).patchValue A.kernel = _
  rw [WeightedParameterSlots.reparam_slots]
  rfl

end WeightedParameterPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3.BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

omit [DecidableEq ι] in
theorem normalizedPoint_dist_start (hN : ∀ i, 0 < N i) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (a : ∀ i, (P i).Label)
    (hwidth : ∀ i, ((P i).step (a i) : ℝ) * (P i).length (a i) ≤ ρ * N i)
    (j : ∀ i, Fin ((P i).length (a i))) :
    dist (normalizedPoint (point P a j)) (normalizedStart P a) ≤ ρ := by
  apply (dist_pi_le_iff hρ).mpr
  intro i
  have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hj : ((j i).val : ℝ) ≤ (P i).length (a i) := by exact_mod_cast (j i).isLt.le
  rw [Real.dist_eq]
  change |((point P a j i).val : ℝ) / N i - ((P i).start (a i) : ℝ) / N i| ≤ ρ
  rw [point_val, Nat.cast_add, Nat.cast_mul, ← sub_div, add_sub_cancel_left]
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hNi).mpr
  exact (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg _)).trans (hwidth i)

end Erdos3.BoxProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositivePartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_weighted_partition_score {Ω ι : Type*} [Fintype Ω] [Fintype ι] [Nonempty ι]
    (a : Ω → ℝ) (w : ι → Ω → ℝ) (hsum : ∀ x, ∑ i, w i x = 1)
    {S : ℝ} (hS : S ≤ 𝔼 x, a x) :
    ∃ i, S / Fintype.card ι ≤ 𝔼 x, a x * w i x := by
  have htotal : (∑ i, 𝔼 x, a x * w i x) = 𝔼 x, a x := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.mul_sum, hsum, mul_one]
  have hmean : (𝔼 i, 𝔼 x, a x * w i x) = (𝔼 x, a x) / Fintype.card ι := by
    rw [Fintype.expect_eq_sum_div_card, htotal]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (show S / Fintype.card ι ≤ 𝔼 i, 𝔼 x, a x * w i x from
      hmean.symm ▸ div_le_div_of_nonneg_right hS (Nat.cast_nonneg _))
  exact ⟨i, hi⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialPatchComposition
namespace OAI

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

theorem liftInterleaving_before (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (j : Fin D) (i : Fin E) (h : A.weight j ≤ B.weight i) :
    (A.liftInterleaving B).left j < (A.liftInterleaving B).right i :=
  SlotInterleaving.sorted_left_lt_right _ _ _ _ j i h

theorem insertLifts_term (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) (z : Fin (D + E) → ℤ) :
    (A.insertLifts B).kernel.value (((A.insertLifts B).form.slots t).residual z) =
      A.kernel.value ((A.form.slots t).residual (fun j => z ((A.liftInterleaving B).left j))) *
      B.kernel.value ((B.form.slots (Sum.elim t
        (fun j => (z ((A.liftInterleaving B).left j) : ℝ)))).residual
          (fun j => z ((A.liftInterleaving B).right j))) := by
  let I := A.liftInterleaving B
  change A.kernel.value (fun i => ((A.form.insertLifts B.form I).slots t).residual z (I.left i)) *
    B.kernel.value (fun i => ((A.form.insertLifts B.form I).slots t).residual z (I.right i)) = _
  simp only [PolynomialSlots.insertLifts_residual_left,
    PolynomialSlots.insertLifts_residual_right A.form B.form I (A.liftInterleaving_before B)]
  rfl

theorem insertLifts_value_at_lift (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) (b : Fin D → ℤ)
    (hb : ∀ i, |(A.form.slots t).residual b i| ≤ 1 / 3) :
    (A.insertLifts B).value t = A.kernel.value ((A.form.slots t).residual b) *
      B.value (Sum.elim t (fun j => (b j : ℝ))) :=
  (A.form.slots t).factorized_patchValue_at_lift
    (fun b => B.form.slots (Sum.elim t (fun j => (b j : ℝ))))
    ((A.insertLifts B).form.slots t) A.kernel B.kernel (A.insertLifts B).kernel
    (A.liftInterleaving B) (A.insertLifts_term B t) b hb

theorem insertLifts_value (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) :
    (A.insertLifts B).value t = ∑' b : Fin D → ℤ,
      A.kernel.value ((A.form.slots t).residual b) *
        B.value (Sum.elim t (fun j => (b j : ℝ))) :=
  (A.form.slots t).factorized_patchValue
    (fun b => B.form.slots (Sum.elim t (fun j => (b j : ℝ))))
    ((A.insertLifts B).form.slots t) A.kernel B.kernel (A.insertLifts B).kernel
    (A.liftInterleaving B) (A.insertLifts_term B t)

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLiftInsertion
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ ρ : Type*} {D E s : ℕ}

theorem affineLiftSubstitution_eval (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (t : σ → ℝ) (x : Fin D → ℝ) (a : σ ⊕ ρ) :
    aeval (Sum.elim t x) (affineLiftSubstitution c M a) =
      Sum.elim t (fun a => c a + ∑ j, M a j * x j) a := by
  cases a <;> simp [affineLiftSubstitution]

namespace PolynomialPatch

theorem insertAffineLifts_value_at_lift {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a)
    (t : σ → ℝ) (b : Fin D → ℤ)
    (hb : ∀ i, |(A.form.slots t).residual b i| ≤ 1 / 3) :
    (A.insertAffineLifts B c M hM).value t =
      A.kernel.value ((A.form.slots t).residual b) *
        B.value (Sum.elim t (fun a => c a + ∑ j, M a j * (b j : ℝ))) := by
  unfold insertAffineLifts
  rw [insertLifts_value_at_lift _ _ t b hb, WeightedParameterPatch.reparam_value]
  simp only [affineLiftSubstitution_eval]

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidualRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem recoveredSmallLift_at_integer {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a x : Fin d → ℝ) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    recoveredSmallLift M a c (fun j => (k j : ℝ) - (x - a) j) =
      fun i => realIntegerMatrix M x i - (recoveredIntegerLift M c k i : ℝ) := by
  funext i
  simp only [recoveredSmallLift, realIntegerMatrix, recoveredIntegerLift, Pi.sub_apply]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BufferedIntegerLift
namespace OAI

section

namespace Erdos3

namespace PatchKernel

theorem buffered_sum_eq_nearest {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (f : (Fin m → ℤ) → ℝ) :
    (∑' β, Ψ.value (fun i => x i - (β i : ℝ)) * f β) =
      Ψ.value (fun i => x i - (nearestIntegerLift x i : ℝ)) * f (nearestIntegerLift x) := by
  classical
  apply tsum_eq_single (nearestIntegerLift x)
  intro γ hγ
  have hzero : Ψ.value (fun i => x i - (γ i : ℝ)) = 0 := by
    by_contra hn
    exact hγ (Ψ.buffered_lift_unique x _ γ (nearestIntegerLift_close x) hn)
  rw [hzero, zero_mul]

end PatchKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BufferedKernelFamily
namespace OAI

section

namespace Erdos3.PatchKernel

theorem buffered_family_lift_value_eq {m : ℕ} (Ψ : (Fin m → ℤ) → PatchKernel m)
    (x : Fin m → ℝ) (β γ : Fin m → ℤ)
    (hβ : ∀ i, |x i - (β i : ℝ)| ≤ 1 / 2)
    (hmatch : (Ψ β).value (fun i => x i - (β i : ℝ)) ≠ 0 → γ = β)
    (f : (Fin m → ℤ) → ℝ) :
    (Ψ γ).value (fun i => x i - (γ i : ℝ)) * f γ =
      (Ψ β).value (fun i => x i - (β i : ℝ)) * f β := by
  by_cases h : (Ψ β).value (fun i => x i - (β i : ℝ)) = 0
  · have hzero : (Ψ γ).value (fun i => x i - (γ i : ℝ)) = 0 := by
      by_contra hγ
      have heq := (Ψ γ).buffered_lift_unique x β γ hβ hγ
      exact hγ (by simpa only [heq] using h)
    rw [hzero, h, zero_mul, zero_mul]
  · rw [hmatch h]

theorem buffered_family_sum_eq_nearest {m : ℕ} (Ψ : (Fin m → ℤ) → PatchKernel m)
    (x : Fin m → ℝ) (f : (Fin m → ℤ) → ℝ) :
    (∑' β, (Ψ β).value (fun i => x i - (β i : ℝ)) * f β) =
      (Ψ (nearestIntegerLift x)).value (fun i => x i - (nearestIntegerLift x i : ℝ)) *
        f (nearestIntegerLift x) := by
  classical
  apply tsum_eq_single (nearestIntegerLift x)
  intro γ hγ
  have hzero : (Ψ γ).value (fun i => x i - (γ i : ℝ)) = 0 := by
    by_contra hn
    exact hγ ((Ψ γ).buffered_lift_unique x _ γ (nearestIntegerLift_close x) hn)
  rw [hzero, zero_mul]

end Erdos3.PatchKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PeriodicKernelPartition
namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem translateSum_integer_periodic (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x : Fin d → ℝ) (m : Fin d → ℤ) :
    Φ.translateSum c (fun j => x j + m j) = Φ.translateSum c x := by
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun j => x j + (m j : ℝ)) - c i = fun j => (x - c i) j + m j := by
    funext j
    simp only [Pi.sub_apply]
    ring
  rw [heq, Φ.periodicValue_integer_periodic]

theorem normalizedTranslate_periodicValue (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hcover : ∀ x, (δ : ℝ) ≤ Φ.translateSum c x)
    (i : ι) (x : Fin d → ℝ) :
    (Φ.normalizedTranslate c δ hδ hcover i).periodicValue (x - c i) =
      Φ.periodicValue (x - c i) / Φ.translateSum c x := by
  have hden (b : Fin d → ℤ) :
      Φ.translateSum c (c i - fun j => (b j : ℝ) - (x - c i) j) = Φ.translateSum c x := by
    have heq : c i - (fun j => (b j : ℝ) - (x - c i) j) = fun j => x j + ((-b j : ℤ) : ℝ) := by
      funext j
      simp only [Pi.sub_apply, Int.cast_neg]
      ring
    rw [heq, Φ.translateSum_integer_periodic]
  change (∑' b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - (x - c i) j) /
    Φ.translateSum c (c i - fun j => (b j : ℝ) - (x - c i) j)) = _
  simp only [hden]
  exact tsum_div_const

theorem sum_normalizedTranslate_periodicValue (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hcover : ∀ x, (δ : ℝ) ≤ Φ.translateSum c x)
    (x : Fin d → ℝ) :
    (∑ i, (Φ.normalizedTranslate c δ hδ hcover i).periodicValue (x - c i)) = 1 := by
  simp only [normalizedTranslate_periodicValue, ← Finset.sum_div]
  exact div_self (ne_of_gt (lt_of_lt_of_le hδ (hcover x)))

end Erdos3.PatchKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCellBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem torusGridKernel_lip (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) :
    (torusGridKernel d q hq a).lip = (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) := by
  norm_num [torusGridKernel, PatchKernel.normalizedTranslate, localTentKernel]
  ring

theorem sum_torusGridKernel_periodicValue (d q : ℕ) (hq : 8 ≤ q) (x : Fin d → ℝ) :
    (∑ a : Fin d → Fin q, (torusGridKernel d q hq a).periodicValue (x - torusGridCenter q a)) = 1 :=
  (localTentKernel d q hq).sum_normalizedTranslate_periodicValue (torusGridCenter q)
    (1 / 2) (by norm_num) (fun x => by simpa using localTent_translateSum_ge_half d q hq x) x

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators NNReal

variable {σ : Type*} {s d : ℕ}

theorem polynomialTorusCell_lip (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) :
    (polynomialTorusCell w hw hws hmono P hP q hq a).kernel.lip =
      (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) := torusGridKernel_lip d q hq a

end Erdos3

end

section

namespace Erdos3

namespace PatchKernel

variable {d : ℕ}

theorem periodicValue_eq_integerLift (Φ : PatchKernel d) (x : Fin d → ℝ) :
    Φ.periodicValue x = Φ.value (fun j => (Φ.integerLift x j : ℝ) - x j) := by
  classical
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) ≠ 0
  · simp only [integerLift, dif_pos h]
    exact (constantSlots x).patchValue_eq_of_nonzero Φ h.choose_spec
  · have hz : ∀ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) = 0 := by simpa using h
    have hp : Φ.periodicValue x = 0 := (constantSlots x).patchValue_eq_zero Φ hz
    simpa only [integerLift, dif_neg h, hz] using hp

theorem integerLift_contributes (Φ : PatchKernel d) (x : Fin d → ℝ)
    (hx : Φ.periodicValue x ≠ 0) : Φ.value (fun j => (Φ.integerLift x j : ℝ) - x j) ≠ 0 := by
  rwa [← Φ.periodicValue_eq_integerLift x]

end PatchKernel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer
namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ}

theorem weightBounded_value (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (x : Fin d → ℝ) :
    (Φ.weightBounded f L C hC hf hbound).value x = Φ.value x * f x / C := by
  change Φ.value x * (f x / C) = _
  ring

end Erdos3.PatchKernel

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal

variable {σ : Type*} {s d E m : ℕ} {p : Fin m → ℕ}

theorem insertAffineLifts_value (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (c : Fin m → ℝ) (M : Fin m → Fin d → ℝ)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) (t : σ → ℝ) :
    (A.insertAffineLifts B c M hweight).value t = ∑' k : Fin d → ℤ,
      A.kernel.value ((A.form.slots t).residual k) *
        B.value (Sum.elim t (fun i => c i + ∑ j, M i j * (k j : ℝ))) := by
  unfold insertAffineLifts
  rw [insertLifts_value]
  apply tsum_congr
  intro k
  rw [WeightedParameterPatch.reparam_value]
  simp only [affineLiftSubstitution_eval]

theorem recoveredPatch_value_at_lift (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i)
    (t : σ → ℝ) (x : Fin d → ℝ) (hslots : A.form.slots t = constantSlots (x - a))
    (k : Fin d → ℤ) (hk : ∀ j, |(k j : ℝ) - (x - a) j| ≤ 1 / 3) :
    (A.recoveredPatch B Ψ M a c K hM hweight).value t =
      A.kernel.value (fun j => (k j : ℝ) - (x - a) j) *
        Ψ.value (fun i => realIntegerMatrix M x i - (recoveredIntegerLift M c k i : ℝ)) *
        B.value (Sum.elim t (fun i => (recoveredIntegerLift M c k i : ℝ))) := by
  have hres : (A.form.slots t).residual k = fun j => (k j : ℝ) - (x - a) j := by
    rw [hslots]
    rfl
  unfold recoveredPatch
  rw [insertAffineLifts_value_at_lift _ _ _ _ _ t k (by simpa only [withRecoveredWeight, hres] using hk)]
  change (recoveredCellKernel A.kernel Ψ M a c K hM).value ((A.form.slots t).residual k) * _ = _
  rw [hres, recoveredCellKernel_value, recoveredSmallLift_at_integer]
  simp only [recoveredIntegerLift, Int.cast_add, Int.cast_sum, Int.cast_mul]

theorem recoveredPatch_value (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i)
    (t : σ → ℝ) (x : Fin d → ℝ) (hslots : A.form.slots t = constantSlots (x - a)) :
    let k := A.kernel.integerLift (x - a)
    (A.recoveredPatch B Ψ M a c K hM hweight).value t =
      A.kernel.periodicValue (x - a) *
        Ψ.value (fun i => realIntegerMatrix M x i - (recoveredIntegerLift M c k i : ℝ)) *
        B.value (Sum.elim t (fun i => (recoveredIntegerLift M c k i : ℝ))) := by
  intro k
  by_cases hactive : A.kernel.periodicValue (x - a) = 0
  · rw [hactive, zero_mul, zero_mul]
    unfold recoveredPatch
    rw [insertAffineLifts_value]
    calc
      _ = ∑' _b : Fin d → ℤ, (0 : ℝ) := by
        apply tsum_congr
        intro b
        have hb : A.kernel.value (fun j => (b j : ℝ) - (x - a) j) = 0 :=
          le_antisymm (by simpa only [hactive] using A.kernel.kernel_le_periodicValue (x - a) b)
            (A.kernel.nonneg _)
        change (A.kernel.value ((A.form.slots t).residual b) * _) * _ = 0
        rw [hslots]
        change (A.kernel.value (fun j => (b j : ℝ) - (x - a) j) * _) * _ = 0
        rw [hb, zero_mul, zero_mul]
      _ = 0 := tsum_zero
  · have hk : ∀ j, |(k j : ℝ) - (x - a) j| ≤ 1 / 3 := fun j =>
      (A.kernel.support _ (A.kernel.integerLift_contributes _ hactive) j).trans (by norm_num)
    rw [A.recoveredPatch_value_at_lift B Ψ M a c K hM hweight t x hslots k hk,
      A.kernel.periodicValue_eq_integerLift]

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

namespace PolynomialPatch

theorem recoveredPatch_value_eq_family {σ : Type*} {s d E m : ℕ} {p : Fin m → ℕ}
    (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : (Fin m → ℤ) → PatchKernel m) (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i)
    (hinvariant : ∀ k, (Ψ (recoveredIntegerLift M c k)).value = (Ψ c).value)
    (t : σ → ℝ) (x : Fin d → ℝ) (hslots : A.form.slots t = constantSlots (x - a))
    (β : Fin m → ℤ) (hβ : ∀ i, |realIntegerMatrix M x i - (β i : ℝ)| ≤ 1 / 2)
    (hmatch : A.kernel.periodicValue (x - a) ≠ 0 →
      (Ψ β).value (fun i => realIntegerMatrix M x i - (β i : ℝ)) ≠ 0 →
      recoveredIntegerLift M c (A.kernel.integerLift (x - a)) = β) :
    (A.recoveredPatch B (Ψ c) M a c K hM hweight).value t =
      A.kernel.periodicValue (x - a) * (Ψ β).value (fun i => realIntegerMatrix M x i - (β i : ℝ)) *
        B.value (Sum.elim t (fun i => (β i : ℝ))) := by
  rw [A.recoveredPatch_value B (Ψ c) M a c K hM hweight t x hslots]
  by_cases h : A.kernel.periodicValue (x - a) = 0
  · simp only [h, zero_mul]
  · simp only [mul_assoc]
    apply congrArg (fun z => A.kernel.periodicValue (x - a) * z)
    rw [← hinvariant (A.kernel.integerLift (x - a))]
    exact PatchKernel.buffered_family_lift_value_eq Ψ (realIntegerMatrix M x) β _ hβ
      (hmatch h) (fun β => B.value (Sum.elim t (fun i => (β i : ℝ))))

end PolynomialPatch

theorem exists_fiberwise_recovered_patch {σ Ω : Type*} [Fintype Ω] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : (Fin m → ℤ) → PatchKernel m)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ c k, (Ψ (recoveredIntegerLift M c k)).value = (Ψ c).value)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hscore : S ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      (Ψ β).value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ (c : Fin m → ℤ) (Q : PolynomialPatch σ s (d + E)),
      Q.kernel.lip = (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) + (Ψ c).lip * K + B.kernel.lip ∧
      S / (q : ℝ) ^ d ≤ 𝔼 u, score u * Q.value (t u) := by
  classical
  let x : Ω → Fin d → ℝ := fun u j => aeval (t u) (P j)
  let β : Ω → Fin m → ℤ := fun u => nearestIntegerLift (realIntegerMatrix M (x u))
  let H : Ω → ℝ := fun u => (Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) *
    B.value (Sum.elim (t u) (fun i => (β u i : ℝ)))
  have hS : S ≤ 𝔼 u, score u * H u := by
    simpa only [PatchKernel.buffered_family_sum_eq_nearest] using hscore
  let cell : (Fin d → Fin q) → Ω → ℝ :=
    fun a u => (torusGridKernel d q hq a).periodicValue (x u - torusGridCenter q a)
  let : NeZero q := ⟨by omega⟩
  obtain ⟨a, ha⟩ := exists_weighted_partition_score (fun u => score u * H u) cell
    (fun u => sum_torusGridKernel_periodicValue d q hq (x u)) hS
  have hcellscore : S / (q : ℝ) ^ d ≤ 𝔼 u, (score u * H u) * cell a u := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using ha
  let active : Set Ω := {u | cell a u ≠ 0 ∧
    (Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) ≠ 0}
  obtain ⟨c, hc⟩ := exists_torusCell_affine_recovery_s2 hq active M a x β hM hmesh
    (fun u hu => hu.1) (fun u hu => (Ψ (β u)).support _ hu.2)
  let A := polynomialTorusCell w hw hws hmono P hP q hq a
  have hweightA : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i := hweight
  let Q := A.recoveredPatch B (Ψ c) M (torusGridCenter q a) c K hM hweightA
  refine ⟨c, Q, ?_, ?_⟩
  · change A.kernel.lip + (Ψ c).lip * K + B.kernel.lip = _
    exact congrArg (fun L => L + (Ψ c).lip * K + B.kernel.lip)
      (polynomialTorusCell_lip w hw hws hmono P hP q hq a)
  · have hvalue (u : Ω) : Q.value (t u) = cell a u * H u := by
      have hslots : A.form.slots (t u) = constantSlots (x u - torusGridCenter q a) := by
        apply TriangularSlots.ext
        intro z j
        have hshift : ∀ i, P i - C (torusGridCenter q a i) ∈
            weightedSupportLE (fun _ : σ => 1) (w i) :=
          fun i => (weightedSupportLE _ _).sub_mem (hP i) (weightedSupportLE_C _ _ _)
        change ((PolynomialSlots.ofCoordinates (w := w)
          (fun i => P i - C (torusGridCenter q a i)) hshift).slots (t u)).center z j = _
        rw [PolynomialSlots.ofCoordinates_center]
        simp [constantSlots, x]
      have hmatch : A.kernel.periodicValue (x u - torusGridCenter q a) ≠ 0 →
          (Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) ≠ 0 →
          recoveredIntegerLift M c (A.kernel.integerLift (x u - torusGridCenter q a)) = β u := by
        intro h₁ h₂
        exact (hc u ⟨h₁, h₂⟩).symm
      change (A.recoveredPatch B (Ψ c) M (torusGridCenter q a) c K hM hweightA).value (t u) =
        A.kernel.periodicValue (x u - torusGridCenter q a) *
          ((Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) *
            B.value (Sum.elim (t u) (fun i => (β u i : ℝ))))
      simpa only [mul_assoc] using A.recoveredPatch_value_eq_family B Ψ M (torusGridCenter q a)
        c K hM hweightA (hinvariant c) (t u) (x u) hslots (β u) (nearestIntegerLift_close _) hmatch
    apply hcellscore.trans_eq
    apply Finset.expect_congr rfl
    intro u _
    rw [hvalue]
    ring

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

theorem exists_fiberwise_weighted_patch {σ Ω : Type*} [Fintype Ω] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : (Fin m → ℤ) → (Fin m → ℝ) → ℝ) (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ β, LipschitzWith L (F β)) (hFbound : ∀ β y, F β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ c k, F (recoveredIntegerLift M c k) = F c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hscore : S ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        F β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      S / ((C : ℝ) * (q : ℝ) ^ d) ≤ 𝔼 u, score u * Q.value (t u) := by
  let Ψ : (Fin m → ℤ) → PatchKernel m := fun β => χ.weightBounded (F β) L C hC (hF β) (hFbound β)
  have hΨ : ∀ c k, (Ψ (recoveredIntegerLift M c k)).value = (Ψ c).value := by
    intro c k
    funext y
    simp only [Ψ, PatchKernel.weightBounded_value, hinvariant]
  have hnormalized : S / (C : ℝ) ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      (Ψ β).value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ))) := by
    apply (div_le_div_of_nonneg_right hscore C.coe_nonneg).trans_eq
    rw [Finset.expect_div]
    apply Finset.expect_congr rfl
    intro u _
    simp only [Ψ, PatchKernel.weightBounded_value, div_mul_eq_mul_div]
    rw [tsum_div_const]
    ring
  obtain ⟨c, Q, hQlip, hQscore⟩ := exists_fiberwise_recovered_patch w hw hws hmono P hP p B Ψ
    M K hM hweight hΨ q hq hmesh t score hnormalized
  exact ⟨Q, hQlip.le, by simpa only [div_div] using hQscore⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeMarkedFreezingSliceScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

theorem exists_long_spatially_frozen_box {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i)
    (score : (∀ i, Fin (N i)) → ℝ) (F : (ι → ℝ) → (∀ i, Fin (N i)) → ℝ)
    (Λ : ℝ≥0) (hF : ∀ x, LipschitzWith Λ (fun z => F z x))
    {C τ ρ S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hscoreBound : ∀ x, |score x| ≤ 1)
    (hcap : ∀ x, F (normalizedPoint x) x ∈ Set.Icc (0 : ℝ) C)
    (hwidth : ∀ a : ∀ i, (P i).Label, ∀ i,
      ((P i).step (a i) : ℝ) * (P i).length (a i) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 x, score x * F (normalizedPoint x) x)
    (hbudget : τ + Λ * ρ + C * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S) :
    ∃ a : ∀ i, (P i).Label, (∀ i, L i ≤ ((P i).length (a i) : ℝ)) ∧
      τ < 𝔼 j : (∀ i, Fin ((P i).length (a i))),
        score (point P a j) * F (normalizedStart P a) (point P a j) := by
  apply exists_long_frozen_box P hN L hL score (fun x => F (normalizedPoint x) x)
    (fun a x => F (normalizedStart P a) x) hC hτ (mul_nonneg Λ.coe_nonneg hρ) hscoreBound
    _ _ hscore hbudget
  · intro x
    have hs : score x ≤ 1 := (le_abs_self _).trans (hscoreBound x)
    exact (mul_le_mul_of_nonneg_right hs (hcap x).1).trans (by simpa using (hcap x).2)
  · intro x
    have hid : point P (cell P x) (fun i => (P i).offset (x i)) = x := by
      funext i
      exact (P i).point_cell_offset (x i)
    have hd := normalizedPoint_dist_start P hN hρ (cell P x) (hwidth (cell P x))
      (fun i => (P i).offset (x i))
    rw [hid] at hd
    exact ((hF x).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd Λ.coe_nonneg)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedPatchEndpoint
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

theorem exists_spatially_frozen_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (q : ℕ) (hq : 0 < q)
    (score : (∀ i, Fin (N i)) → ℝ) (F : (ι → ℝ) → (∀ i, Fin (N i)) → ℝ)
    (Λ : ℝ≥0) (hF : ∀ x, LipschitzWith Λ (fun z => F z x))
    {C τ ρ θ S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ)
    (hscoreBound : ∀ x, |score x| ≤ 1)
    (hcap : ∀ x, F (normalizedPoint x) x ∈ Set.Icc (0 : ℝ) C)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 x, score x * F (normalizedPoint x) x)
    (hbudget : τ + Λ * ρ + C * θ < S) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) ∧
      (∀ i, 0 < A.length i) ∧
      τ < 𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * F A.center (A.point j) := by
  obtain ⟨H, hH, hfit, hwidth, hlower⟩ := exists_box_block_mesh N q hq hρ hρ1 hlarge
  let P := fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)
  let L : ι → ℝ := fun i => θ * H i / (2 * (Fintype.card ι + 1))
  have hL (i) : 0 ≤ L i := by dsimp only [L]; positivity
  have hsmall : (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) ≤ θ :=
    boxBlock_short_side_budget N H q hN hH hfit hθ.le
  have hwidthP (a : ∀ i, (P i).Label) (i) :
      ((P i).step (a i) : ℝ) * (P i).length (a i) ≤ ρ * N i := by
    have hlen : ((P i).length (a i) : ℝ) ≤ H i := by
      exact_mod_cast truncatedProgressionLength_le (N i) (progressionBlockStart (a i)) q (H i)
    exact (mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg q)).trans (hwidth i)
  obtain ⟨a, ha, hs⟩ := exists_long_spatially_frozen_box P hN L hL score F Λ hF hC hτ hρ.le
    hscoreBound hcap hwidthP hscore
    ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall hC)).trans_lt hbudget)
  let A := ResidueBoxSlice.ofBlocks H hq hH a
  have hlen (i) : θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) ≤ (A.length i : ℝ) := by
    apply le_trans _ (ha i)
    dsimp only [L]
    calc
      _ = θ * (ρ * N i / (2 * q)) / (2 * (Fintype.card ι + 1)) := by
        have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
        have hn0 : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hlower i) hθ.le) (by positivity)
  refine ⟨A, hlen, ?_, ?_⟩
  · intro i
    have hp : (0 : ℝ) < θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) := by
      have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
      have hqi : (0 : ℝ) < q := by exact_mod_cast hq
      positivity
    exact_mod_cast hp.trans_le (hlen i)
  · have hcenter : A.center = normalizedStart P a := rfl
    have hpoint (j : ∀ i, Fin (A.length i)) : A.point j = point P a j :=
      ResidueBoxSlice.ofBlocks_point H hq hH a j
    simpa only [hcenter, hpoint] using hs

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem bufferedSpatialWeight_eq_nearest {Ω Θ : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) (z : Θ) (u : Ω) :
    bufferedSpatialWeight χ x T G z u =
      χ.value (fun i => x u i - (nearestIntegerLift (x u) i : ℝ)) *
        G z u (nearestIntegerLift (x u)) * T u (nearestIntegerLift (x u)) := by
  simpa only [bufferedSpatialWeight, mul_assoc] using
    χ.buffered_sum_eq_nearest (x u) (fun b => G z u b * T u b)

theorem bufferedSpatialWeight_mem_Icc {Ω Θ : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) {C : ℝ}
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ z u b, G z u b ∈ Set.Icc (0 : ℝ) C) (z : Θ) (u : Ω) :
    bufferedSpatialWeight χ x T G z u ∈ Set.Icc (0 : ℝ) C := by
  rw [bufferedSpatialWeight_eq_nearest]
  have ht := hT u (nearestIntegerLift (x u))
  have hg := hG z u (nearestIntegerLift (x u))
  constructor
  · exact mul_nonneg (mul_nonneg (χ.nonneg _) hg.1) ht.1
  · calc
      _ = (χ.value _ * T u (nearestIntegerLift (x u))) * G z u (nearestIntegerLift (x u)) := by ring
      _ ≤ G z u (nearestIntegerLift (x u)) :=
        mul_le_of_le_one_left hg.1 ((mul_le_of_le_one_left ht.1 (χ.le_one _)).trans ht.2)
      _ ≤ C := hg.2

theorem bufferedSpatialWeight_lipschitz {Ω Θ : Type*} [PseudoMetricSpace Θ] {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) (Λ : ℝ≥0)
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ u b, LipschitzWith Λ (fun z => G z u b)) (u : Ω) :
    LipschitzWith Λ (fun z => bufferedSpatialWeight χ x T G z u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [bufferedSpatialWeight_eq_nearest, bufferedSpatialWeight_eq_nearest, Real.dist_eq]
  let b := nearestIntegerLift (x u)
  let c := χ.value (fun i => x u i - (b i : ℝ)) * T u b
  have hc0 : 0 ≤ c := mul_nonneg (χ.nonneg _) (hT u b).1
  have hc1 : c ≤ 1 := (mul_le_of_le_one_left (hT u b).1 (χ.le_one _)).trans (hT u b).2
  have heq : χ.value (fun i => x u i - (b i : ℝ)) * G z u b * T u b -
      χ.value (fun i => x u i - (b i : ℝ)) * G w u b * T u b = c * (G z u b - G w u b) := by
    dsimp only [c]
    ring
  change |χ.value _ * G z u b * T u b - χ.value _ * G w u b * T u b| ≤ _
  rw [heq, abs_mul, abs_of_nonneg hc0]
  exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans
    (by simpa only [Real.dist_eq] using (hG u b).dist_le_mul z w)

theorem exists_spatially_frozen_buffered_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (q : ℕ) (hq : 0 < q) {m : ℕ}
    (χ : PatchKernel m) (x : (∀ i, Fin (N i)) → Fin m → ℝ)
    (T : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    (G : (ι → ℝ) → (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    (score : (∀ i, Fin (N i)) → ℝ) (Λ : ℝ≥0)
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ u b, LipschitzWith Λ (fun z => G z u b))
    {C τ ρ θ S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ)
    (hGcap : ∀ z u b, G z u b ∈ Set.Icc (0 : ℝ) C)
    (hscoreBound : ∀ u, |score u| ≤ 1) (hlarge : ∀ i, 2 * (q : ℝ) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 u, score u * bufferedSpatialWeight χ x T G (BoxProgressionPartition.normalizedPoint u) u)
    (hbudget : τ + Λ * ρ + C * θ < S) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) ∧
      (∀ i, 0 < A.length i) ∧
      τ < 𝔼 j : (∀ i, Fin (A.length i)),
        score (A.point j) * bufferedSpatialWeight χ x T G A.center (A.point j) := by
  exact exists_spatially_frozen_slice N hN q hq score (bufferedSpatialWeight χ x T G) Λ
    (bufferedSpatialWeight_lipschitz χ x T G Λ hT hG) hC hτ hρ hρ1 hθ hscoreBound
    (fun u => bufferedSpatialWeight_mem_Icc χ x T G hT hGcap _ u) hlarge hscore hbudget

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal BigOperators

theorem ResidueBoxSlice.point_cast {ι : Type*} {N : ι → ℕ} {q : ℕ}
    (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) :
    (fun i => ((A.point j i).val : ZMod q)) = fun i => (A.start i : ZMod q) := by
  funext i
  simp [ResidueBoxSlice.point]

theorem exists_spatially_localized_patch_s2_oai {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (ι → ℝ) → (ι → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ L C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith L (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : (∀ i, Fin (N i)) → σ → ℝ) (score : (∀ i, Fin (N i)) → ℝ)
    {τ ρ θ S : ℝ} (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ)
    (hscoreBound : ∀ u, |score u| ≤ 1) (hlarge : ∀ i, 2 * (q₀ : ℝ) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 u, score u * ∑' b : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (b i : ℝ)) *
        G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) b
          (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (b i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (b i : ℝ))))
    (hbudget : τ + Λ * ρ + C * θ < S) :
    ∃ (A : ResidueBoxSlice N q₀) (Q : PolynomialPatch σ s (d + E)),
      (∀ i, θ * ρ * N i / (4 * q₀ * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) ∧
      (∀ i, 0 < A.length i) ∧
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      τ / ((C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * Q.value (t (A.point j)) := by
  let x : (∀ i, Fin (N i)) → Fin m → ℝ :=
    fun u => realIntegerMatrix M (fun j => aeval (t u) (P j))
  let T : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ :=
    fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))
  let W : (ι → ℝ) → (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ :=
    fun z u b => G z (fun i => ((u i).val : ZMod q₀)) b (fun i => x u i - (b i : ℝ))
  obtain ⟨A, hlength, hpos, hs⟩ := exists_spatially_frozen_buffered_slice N hN q₀ hq₀ χ x T W
    score Λ (fun u b => B.value_mem_Icc _) (fun u b => hGspace _ _ _) C.coe_nonneg hτ hρ hρ1 hθ
    (fun z u b => hGcap _ _ _ _) hscoreBound hlarge hscore hbudget
  let F := G A.center (fun i => (A.start i : ZMod q₀))
  have hlocalized : τ ≤ 𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * ∑' b : Fin m → ℤ,
      χ.value (fun i => x (A.point j) i - (b i : ℝ)) *
        F b (fun i => x (A.point j) i - (b i : ℝ)) * T (A.point j) b := by
    apply hs.le.trans_eq
    apply Finset.expect_congr rfl
    intro j _
    apply congrArg (fun a => score (A.point j) * a)
    apply tsum_congr
    intro b
    change χ.value _ * G A.center (fun i => ((A.point j i).val : ZMod q₀)) b _ * _ = _
    rw [A.point_cast j]
  obtain ⟨Q, hQlip, hQscore⟩ := exists_fiberwise_weighted_patch w hw hws hmono P hP p B χ F L C hC
    (hGlift A.center _) (hGcap A.center _) M K hM hweight (hinvariant A.center _) q hq hmesh
    (fun j => t (A.point j)) (fun j => score (A.point j)) hlocalized
  exact ⟨A, Q, hlength, hpos, hQlip, hQscore⟩

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.exists_spatially_localized_patch_s2_oai.{u_1, u_2} := @OAI.Erdos3.exists_spatially_localized_patch_s2_oai.{u_1, u_2}
