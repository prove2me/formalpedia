-- Prove2me | solution 1 for OAI.Erdos3.exists_initial_relative_absolute_rule_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:42:14.474642+00:00
-- url     : https://prove2.me/submissions/3befb7c0-e7a9-4996-ae24-63c5c87281bc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B248
import Theorems.Thm_OAI_Erdos3_exists_absolute_crt_window_s2
import Theorems.Thm_OAI_Erdos3_exists_scored_cyclic_patch_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

theorem patch_term {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ) :
    (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) =
      w.value (aeval t P - (b 0 : ℝ)) := by
  simp only [patch, PolynomialPatch.ofCoordinates, kernel, TriangularSlots.residual,
    PolynomialSlots.ofCoordinates_center, map_sub, aeval_C, Algebra.algebraMap_self_apply]
  congr 1
  ring

theorem patch_value {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) (t : σ → ℝ) :
    (w.patch s hs P hP).value t = w.value (Int.fract (aeval t P)) := by
  change (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
    (((w.patch s hs P hP).form.slots t).residual b)) = _
  simp_rw [w.patch_term s hs P hP t]
  rw [tsum_eq_single (fun _ : Fin 1 => ⌊aeval t P⌋)]
  · rfl
  · intro b hb
    by_contra h
    obtain ⟨h0, h1⟩ := w.interior _ h
    have hfloor : ⌊aeval t P⌋ = b 0 := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    apply hb
    funext i
    fin_cases i
    exact hfloor.symm

theorem patch_contributing_lift {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ)
    (hb : (w.patch s hs P hP).kernel.value
      (((w.patch s hs P hP).form.slots t).residual b) ≠ 0) :
    b 0 = ⌊aeval t P⌋ := by
  rw [w.patch_term s hs P hP t] at hb
  obtain ⟨h0, h1⟩ := w.interior _ hb
  exact (Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩).symm

end RepresentativeWindow
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtIntegerRepresentative_cast (u : J → ℤ) :
    (crtIntegerRepresentative N hN u : ZMod (∏ j, N j)) =
      (ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j))) := by
  let E := ZMod.prodEquivPi N hN
  have hcoeff (j : J) : (crtIntegerCoefficient N hN j : ZMod (∏ j, N j)) =
      E.symm (Pi.single j (1 : ZMod (N j))) := by
    simp only [crtIntegerCoefficient, Int.cast_natCast, ZMod.natCast_zmod_val, E]
  calc
    _ = ∑ j, E.symm (Pi.single j (1 : ZMod (N j))) * (u j : ZMod (∏ j, N j)) := by
      simp only [crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, hcoeff]
    _ = E.symm (∑ j, Pi.single j (1 : ZMod (N j)) * (u j : (j : J) → ZMod (N j))) := by
      simp only [map_sum, map_mul, map_intCast]
    _ = _ := by
      congr 1
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_eq_same, one_mul]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij.symm, zero_mul]
      · simp

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_eval (u : J → ℤ) :
    aeval (fun j => (u j : ℝ)) (crtRepresentativePolynomial N hN) =
      (crtIntegerRepresentative N hN u : ℝ) / (∏ i, N i : ℕ) := by
  simp only [crtRepresentativePolynomial, map_sum, map_smul, aeval_X,
    smul_eq_mul, crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRepresentativeFraction
namespace OAI

section

namespace Erdos3

theorem integer_fraction_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    Int.fract ((a : ℝ) / N) = (((a : ZMod N).val : ℝ) / N) := by
  rw [Int.fract_div_intCast_eq_div_intCast_mod]
  exact congrArg (fun z : ℤ => (z : ℝ) / N) (ZMod.val_intCast a).symm

theorem integer_sub_floor_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    a - (N : ℤ) * ⌊(a : ℝ) / N⌋ = ((a : ZMod N).val : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast, ZMod.val_intCast]
  have h := Int.emod_add_mul_ediv a (N : ℤ)
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport
namespace OAI

section

namespace Erdos3.RepresentativeWindow

open _root_.MvPolynomial
open scoped BigOperators

theorem patch_weighted_value {σ : Type*} {N : ℕ} [NeZero N]
    (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (a : ℤ) (he : aeval t P = (a : ℝ) / N) (F : ℤ → ℝ) :
    (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
      (((w.patch s hs P hP).form.slots t).residual b) * F (a - (N : ℤ) * b 0)) =
      w.value (((a : ZMod N).val : ℝ) / N) * F ((a : ZMod N).val) := by
  have hterm (b : Fin 1 → ℤ) :
      (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) *
        F (a - (N : ℤ) * b 0) =
      (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) *
        F ((a : ZMod N).val) := by
    by_cases hb : (w.patch s hs P hP).kernel.value
        (((w.patch s hs P hP).form.slots t).residual b) = 0
    · simp only [hb, zero_mul]
    · rw [w.patch_contributing_lift s hs P hP t b hb, he, integer_sub_floor_eq_zmod_val]
  simp_rw [hterm]
  rw [tsum_mul_right]
  change (w.patch s hs P hP).value t * F ((a : ZMod N).val) = _
  rw [w.patch_value s hs P hP t, he, integer_fraction_eq_zmod_val]

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtPatch_value (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) (u : J → ℤ) :
    (w.crtPatch N hN s hs).value (fun j => (u j : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) := by
  rw [crtPatch, w.patch_value, crtRepresentativePolynomial_eval,
    integer_fraction_eq_zmod_val, crtIntegerRepresentative_cast]

theorem crtPatch_value_residues [∀ j, NeZero (N j)] (w : RepresentativeWindow)
    (s : ℕ) (hs : 1 ≤ s) (u : (j : J) → ZMod (N j)) :
    (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) := by
  have h := w.crtPatch_value N hN s hs (fun j => ((u j).val : ℤ))
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h

theorem crtPatch_weighted_value (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (u : J → ℤ) (F : ℤ → ℝ) :
    (∑' b : Fin 1 → ℤ, (w.crtPatch N hN s hs).kernel.value
      (((w.crtPatch N hN s hs).form.slots (fun j => (u j : ℝ))).residual b) *
        F (crtIntegerRepresentative N hN u - (∏ j, N j : ℕ) * b 0)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) *
      F (((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val) := by
  have h := w.patch_weighted_value s hs (crtRepresentativePolynomial N hN)
    (crtRepresentativePolynomial_degree N hN) (fun j => (u j : ℝ))
    (crtIntegerRepresentative N hN u) (crtRepresentativePolynomial_eval N hN u) F
  simpa only [crtIntegerRepresentative_cast, crtPatch] using h

end Erdos3.RepresentativeWindow

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

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

omit [NeZero (∏ j, N j)] in
theorem crtLiftPolynomial_eval (u : J → ℤ) (b : Fin 1 → ℤ) :
    aeval (Sum.elim (fun j => (u j : ℝ)) (fun i => (b i : ℝ))) (crtLiftPolynomial N hN) =
      ((crtIntegerRepresentative N hN u - (∏ j, N j : ℕ) * b 0 : ℤ) : ℝ) := by
  simp only [crtLiftPolynomial, map_sub, map_sum, map_smul, aeval_X,
    Sum.elim_inl, Sum.elim_inr, smul_eq_mul, crtIntegerRepresentative,
    Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

namespace RepresentativeWindow

variable (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) {d : ℕ}

theorem composeCRTPatch_value (P : PolynomialPatch Unit s d) (u : J → ℤ) :
    (w.composeCRTPatch N hN s hs P).value (fun j => (u j : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) *
      P.value (fun _ => (((ZMod.prodEquivPi N hN).symm
        (fun j => (u j : ZMod (N j)))).val : ℝ)) := by
  rw [composeCRTPatch, PolynomialPatch.insertLifts_value]
  simpa only [WeightedParameterPatch.reparam_value, PolynomialPatch.weightedParameters_value,
    crtLiftPolynomial_eval, Int.cast_natCast] using
    w.crtPatch_weighted_value N hN s hs u (fun n => P.value (fun _ => (n : ℝ)))

theorem composeCRTPatch_value_residues [∀ j, NeZero (N j)]
    (P : PolynomialPatch Unit s d) (u : (j : J) → ZMod (N j)) :
    (w.composeCRTPatch N hN s hs P).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) *
      P.value (fun _ => (((ZMod.prodEquivPi N hN).symm u).val : ℝ)) := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    w.composeCRTPatch_value N hN s hs P (fun j => ((u j).val : ℤ))

omit [NeZero (∏ j, N j)] in

theorem composeCRTPatch_cost (P : PolynomialPatch Unit s d) {p q : ℝ}
    (hP : (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ p)
    (hw : Real.log (2 + (w.lip : ℝ)) ≤ q) :
    ((1 + d : ℕ) : ℝ) +
      Real.log (2 + ((w.composeCRTPatch N hN s hs P).kernel.lip : ℝ)) ≤ p + q + 1 := by
  have hp0 := P.kernel.lip.coe_nonneg
  have hw0 := w.lip.coe_nonneg
  have hlog : Real.log (2 + ((w.lip : ℝ) + P.kernel.lip)) ≤
      Real.log (2 + (w.lip : ℝ)) + Real.log (2 + (P.kernel.lip : ℝ)) := by
    calc
      _ ≤ Real.log ((2 + (w.lip : ℝ)) * (2 + (P.kernel.lip : ℝ))) := by
        apply Real.log_le_log (by positivity)
        nlinarith [mul_nonneg hw0 hp0]
      _ = _ := Real.log_mul (by positivity) (by positivity)
  rw [composeCRTPatch_lip, NNReal.coe_add, Nat.cast_add, Nat.cast_one]
  linarith

end RepresentativeWindow
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScoredCRTWindowPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

universe u

theorem exists_scored_windowed_crt_patch (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
      (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow)
      (a : ((j : J) → ZMod (N j)) → ℝ) {p : ℝ},
      0 ≤ p → PositiveCyclicNiltest.{u} s (∏ j, N j) p T →
      Real.log (2 + (w.lip : ℝ)) ≤ p →
      Real.exp (-p) ≤ (𝔼 x, (a x * T ((ZMod.prodEquivPi N hN).symm x)) *
        w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) →
      ∃ d : ℕ, ∃ P : PolynomialPatch J s d,
        (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤ (𝔼 x, a x * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨A, _, hconvert⟩ := exists_scored_cyclic_patch_s2.{u} s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 2) ^ A + Polynomial.X + 1)
  refine ⟨C, hC, ?_⟩
  intro J _ _ N _ _ hN T w a p hp hT hw hscore
  let b := fun x : (j : J) → ZMod (N j) =>
    a x * w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))
  have hscore' : Real.exp (-p) ≤ (𝔼 x, b x * T ((ZMod.prodEquivPi N hN).symm x)) := by
    have heq : (𝔼 x, b x * T ((ZMod.prodEquivPi N hN).symm x)) =
        (𝔼 x, (a x * T ((ZMod.prodEquivPi N hN).symm x)) *
          w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) := by
      apply Finset.expect_congr rfl
      intro x _
      dsimp only [b]
      ring
    rw [heq]
    exact hscore
  obtain ⟨d, Q, hQ, hscoreQ⟩ := hconvert T b (ZMod.prodEquivPi N hN).symm hp hT hscore'
  let P := w.composeCRTPatch N hN s hs Q
  have hcost : ((1 + d : ℕ) : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤
      (p + 2) ^ A + p + 1 := w.composeCRTPatch_cost N hN s hs Q hQ hw
  have hb : (p + 2) ^ A + p + 1 ≤ (p + 2) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hsame : (𝔼 x, a x * P.value (fun j => ((x j).val : ℝ))) =
      (𝔼 x, b x * Q.value (fun _ => (((ZMod.prodEquivPi N hN).symm x).val : ℝ))) := by
    apply Finset.expect_congr rfl
    intro x _
    rw [show P.value (fun j => ((x j).val : ℝ)) = _ from
      w.composeCRTPatch_value_residues N hN s hs Q x]
    dsimp only [b]
    ring
  refine ⟨1 + d, P, hcost.trans hb, ?_⟩
  rw [hsame]
  exact (Real.exp_le_exp.mpr (neg_le_neg (show (p + 2) ^ A ≤ (p + 2) ^ C by linarith))).trans hscoreQ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AbsoluteCRTPolynomialPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_absolute_crt_patch {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
        (_hprime : ∀ j, (N j).Prime) (_hinj : Function.Injective N)
        (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
        0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (𝔼 x, f x) = alpha →
        IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
        ∃ d : ℕ, ∃ P : PolynomialPatch J (k - 2) d,
          (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
          Real.exp (-((p + 2) ^ C)) ≤
            (𝔼 x, (f x - (1 + xi) * alpha) * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨Csc, _, Cside, hCside, _, Cwindow, _, xi, hxi, hwindow⟩ :=
    exists_absolute_crt_window_s2 (J := J) k hk
  obtain ⟨A, _, hconvert⟩ := exists_scored_windowed_crt_patch.{0} (k - 2) (by omega)
  obtain ⟨B, _, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (((Polynomial.X + 2) ^ (max Csc Cwindow) + 2) ^ A)
  let C := max Cside B
  refine ⟨C, hCside.trans (le_max_left _ _), xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hside : (p + 2) ^ Cside ≤ (p + 2) ^ C :=
    pow_le_pow_right₀ hbase (le_max_left _ _)
  obtain ⟨T, w, hT, hw, hscore⟩ := hwindow N hprime hinj f halpha hp hlog
    (fun j => (Real.exp_le_exp.mpr hside).trans (hsize j)) hf hmean hfree
  let q := (p + 2) ^ (max Csc Cwindow)
  have hq : 0 ≤ q := pow_nonneg (by linarith) _
  have hsc : (p + 2) ^ Csc ≤ q := pow_le_pow_right₀ hbase (le_max_left _ _)
  have hwin : (p + 2) ^ Cwindow ≤ q := pow_le_pow_right₀ hbase (le_max_right _ _)
  let hN := distinct_prime_moduli_coprime N hprime hinj
  have hs : Real.exp (-q) ≤
      (𝔼 x, ((f x - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm x)) *
        w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hwin)).trans
    simpa only [RepresentativeWindow.crtPatch_value_residues] using hscore
  obtain ⟨d, P, hP, hscoreP⟩ := hconvert N hN T w (fun x => f x - (1 + xi) * alpha)
    hq (hT.mono le_rfl hsc) (hw.trans hwin) hs
  have hbound : (q + 2) ^ A ≤ (p + 2) ^ C := by
    apply le_trans _ (pow_le_pow_right₀ hbase (le_max_right _ _))
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp0
  exact ⟨d, P, hP.trans hbound, (Real.exp_le_exp.mpr (neg_le_neg hbound)).trans hscoreP⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProductiveAbsoluteCRTPatches
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem PolynomialPatch.positive_score_target_lt_one {σ Ω : Type*} [Fintype Ω]
    {s d : ℕ} (P : PolynomialPatch σ s d) (t : Ω → σ → ℝ) (f : Ω → ℝ)
    (hf : ∀ x, f x ≤ 1) {b : ℝ}
    (hscore : 0 < 𝔼 x, (f x - b) * P.value (t x)) : b < 1 := by
  by_contra h
  have hb : 1 ≤ b := le_of_not_gt h
  have hnonpos : (𝔼 x, (f x - b) * P.value (t x)) ≤ 0 := by
    calc
      _ ≤ 𝔼 _x : Ω, (0 : ℝ) := Finset.expect_le_expect
        (fun x _ => mul_nonpos_of_nonpos_of_nonneg
          (by linarith [hf x]) (P.value_mem_Icc _).1)
      _ = 0 := by simp
  exact (not_lt_of_ge hnonpos) hscore

theorem exists_absolute_crt_threshold_rule {J : Type*} [Fintype J] [DecidableEq J]
    [Nonempty J] (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)],
        (∀ j, (N j).Prime) → Function.Injective N →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        ∀ f : ((j : J) → ZMod (N j)) → ℝ,
          (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → a ≤ (𝔼 x, f x) →
          IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
          (1 + xi) * a < 1 ∧ ∃ d : ℕ, ∃ P : PolynomialPatch J (k - 2) d,
            (d : ℝ) ≤ (p + 2) ^ C ∧
            (P.kernel.lip : ℝ) + 1 ≤ Real.exp ((p + 2) ^ C) ∧
            Real.exp (-((p + 2) ^ C)) ≤
              (𝔼 x, (f x - (1 + xi) * a) * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨C, hC, xi, hxi, hpatch⟩ := exists_absolute_crt_patch (J := J) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro p a hp ha N _ _ hprime hinj hsize f hf hmean hfree
  let alpha := 𝔼 x, f x
  have halpha : 0 < alpha := (Real.exp_pos (-p)).trans_le (ha.trans hmean)
  have hlog : Real.log (1 / alpha) ≤ p := by
    rw [one_div, Real.log_inv]
    have h := Real.log_le_log (Real.exp_pos (-p)) (ha.trans hmean)
    rw [Real.log_exp] at h
    linarith
  obtain ⟨d, P, hcost, hscore⟩ := hpatch N hprime hinj f halpha hp hlog hsize hf rfl hfree
  have hlognonneg : 0 ≤ Real.log (2 + (P.kernel.lip : ℝ)) :=
    Real.log_nonneg (by linarith [P.kernel.lip.coe_nonneg])
  have hlip : Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C := by
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hscore' : Real.exp (-((p + 2) ^ C)) ≤
      (𝔼 x, (f x - (1 + xi) * a) * P.value (fun j => ((x j).val : ℝ))) := by
    apply hscore.trans
    apply Finset.expect_le_expect
    intro x _
    apply mul_le_mul_of_nonneg_right _ (P.value_mem_Icc _).1
    have h := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 1 + xi by linarith)
    dsimp only [alpha] at *
    linarith
  refine ⟨P.positive_score_target_lt_one _ f (fun x => (hf x).2)
    ((Real.exp_pos _).trans_le hscore'), d, P, by linarith, ?_, hscore'⟩
  · have h := Real.exp_le_exp.mpr hlip
    rw [Real.exp_log (by positivity : 0 < 2 + (P.kernel.lip : ℝ))] at h
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerBox_real_expect_eq_residue {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) [∀ i, NeZero (N i)] (f : (X → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox N, f x) = 𝔼 u, f (residueBoxIntegerPoint N u) := by
  symm
  apply Finset.expect_bij (fun u _ => residueBoxIntegerPoint N u)
  · intro u _
    exact (mem_integerBox N _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by
        change ((u i).val : ℤ) < N i
        exact_mod_cast (u i).val_lt⟩)
  · intro u _
    rfl
  · intro u _ v _ h
    funext i
    apply ZMod.val_injective
    have hi := congrFun h i
    dsimp only [residueBoxIntegerPoint] at hi
    exact_mod_cast hi
  · intro x hx
    have hx' := (mem_integerBox N x).mp hx
    refine ⟨fun i => (x i : ZMod (N i)), Finset.mem_univ _, ?_⟩
    funext i
    dsimp only [residueBoxIntegerPoint]
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

theorem relativePatchSliceScore_identity {X : Type*} [Fintype X]
    {s d : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) :
    relativePatchSliceScore (ResidueBoxSlice.identity N) f a A =
      relativePatchBoxScore N f a A := by
  unfold relativePatchSliceScore relativePatchBoxScore
  simp only [ResidueBoxSlice.identity, ResidueBoxSlice.point, zero_add, one_mul]
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    exact (mem_integerBox N _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩)
  · intro t _
    simp only [Int.cast_natCast]
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox N x).mp hx
    refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, Finset.mem_univ _, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

theorem exists_initial_relative_absolute_rule_s2_oai (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
        RelativePatchAbsoluteRule (k - 2) n₀ ((p + 2) ^ (C + 1)) a ((1 + xi) * a)
          ⌊(p + 2) ^ C⌋₊ := by
  obtain ⟨C, hC, xi, hxi, habs⟩ := exists_absolute_crt_threshold_rule (J := Fin n₀) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro p a hp ha N hprime hinj _hcomparable hN f hf hfree hmean
  let : ∀ i, NeZero (N i) := fun i => ⟨(hprime i).ne_zero⟩
  let : NeZero (∏ i, N i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)⟩
  let x := (p + 2) ^ C
  let cost := (p + 2) ^ (C + 1)
  have hx : 0 ≤ x := pow_nonneg (by linarith) _
  have hcost : 2 * x ≤ cost := by
    dsimp only [cost]
    rw [pow_succ]
    change 2 * x ≤ x * (p + 2)
    nlinarith
  have hxcost : x ≤ cost := by linarith
  have hmem (u : ∀ i, ZMod (N i)) : residueBoxIntegerPoint N u ∈ integerBox N :=
    (mem_integerBox N _).mpr (fun i => ⟨Int.natCast_nonneg _, by
      change ((u i).val : ℤ) < N i
      exact_mod_cast (u i).val_lt⟩)
  have hf' : ∀ u, f (residueBoxIntegerPoint N u) ∈ Set.Icc (0 : ℝ) 1 := fun u => hf _ (hmem u)
  have hmean' : a ≤ 𝔼 u, f (residueBoxIntegerPoint N u) := by
    rwa [integerBox_real_expect_eq_residue] at hmean
  have hfree' : IntegerVectorAPFree
      (residueBoxIntegerPoint N '' Function.support (fun u => f (residueBoxIntegerPoint N u))) k := by
    have hfreeK : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k := by
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ k)] using hfree
    intro z d hd
    obtain ⟨i, hi⟩ := hfreeK z d hd
    refine ⟨i, ?_⟩
    rintro ⟨u, hu, he⟩
    apply hi
    rw [← he]
    exact ⟨hmem u, hu⟩
  obtain ⟨_, d, A, hd, hLip, hscore⟩ := habs hp ha N hprime hinj
    (fun i => (Real.exp_le_exp.mpr hxcost).trans (hN i)) (fun u => f (residueBoxIntegerPoint N u))
    hf' hmean' hfree'
  refine ⟨1, by decide, ResidueBoxSlice.identity N, d, A, ?_, Nat.le_floor hd, ?_, ?_⟩
  · intro i
    change Real.exp (-cost) * (N i : ℝ) ≤ (N i : ℝ)
    exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by linarith)) (Nat.cast_nonneg _)).trans_eq (one_mul _)
  · have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ x := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 + A.kernel.lip)
        (by simpa only [add_comm] using hLip)
      rwa [Real.log_exp] at hh
    unfold relativePatchComplexity
    linarith
  · rw [relativePatchSliceScore_identity]
    unfold relativePatchBoxScore
    let : DecidableEq (Fin n₀) := Classical.decEq _
    rw [integerBox_real_expect_eq_residue]
    apply (Real.exp_le_exp.mpr (neg_le_neg hxcost)).trans
    convert hscore using 1
    congr 1
    congr 1
    ext; simp

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_initial_relative_absolute_rule_s2_oai := @OAI.Erdos3.exists_initial_relative_absolute_rule_s2_oai
