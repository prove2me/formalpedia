-- Prove2me | solution 1 for OAI.Erdos3.polynomial_patch_density_increment_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:17:01.789913+00:00
-- url     : https://prove2.me/submissions/cf9ca475-743a-4423-84b9-d6fab38d24a2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B208
import Definitions.Def_OAIE3v2B225
import Theorems.Thm_OAI_Erdos3_exists_polynomial_coordinate_partition_bound_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem patchValue_eq_at_residual {b : Fin d → ℤ}
    (hb : ∀ i, |A.residual b i| ≤ 1 / 4) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.integer_unique (by norm_num) (Φ.support _ hc) hb)

theorem patchValue_dist_le (Ψ : PatchKernel d) {δ : ℝ} (hδ : 0 ≤ δ)
    (herror : ∀ z, dist (Φ.value z) (Ψ.value z) ≤ δ) :
    dist (A.patchValue Φ) (A.patchValue Ψ) ≤ δ := by
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (A.residual b) ≠ 0 ∨ Ψ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    have hres : ∀ i, |A.residual b i| ≤ 1 / 4 := hb.elim (Φ.support _) (Ψ.support _)
    rw [A.patchValue_eq_at_residual Φ hres, A.patchValue_eq_at_residual Ψ hres]
    exact herror _
  · have hΦ : ∀ b, Φ.value (A.residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨b, Or.inl hb⟩
    have hΨ : ∀ b, Ψ.value (A.residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨b, Or.inr hb⟩
    rw [A.patchValue_eq_zero Φ hΦ, A.patchValue_eq_zero Ψ hΨ, dist_self]
    exact hδ

end TriangularSlots

end Erdos3

end

section

namespace Erdos3

variable {D E : ℕ}

theorem append_slotPrefix_slotSuffix {R : Type*} (x : Fin (D + E) → R) :
    Fin.append (slotPrefix x) (slotSuffix x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [slotPrefix, slotSuffix]

namespace TriangularSlots

theorem append_residual (A : TriangularSlots D) (B : (Fin D → ℝ) → TriangularSlots E)
    (b : Fin D → ℤ) (c : Fin E → ℤ) :
    (A.append B).residual (Fin.append b c) =
      Fin.append (A.residual b) ((B (fun i => (b i : ℝ))).residual c) := by
  have hp : slotPrefix (D := D) (E := E) (fun j => ((Fin.append b c j : ℤ) : ℝ)) =
      fun i => (b i : ℝ) := by ext i; simp [slotPrefix]
  have hs : slotSuffix (D := D) (E := E) (fun j => ((Fin.append b c j : ℤ) : ℝ)) =
      fun i => (c i : ℝ) := by ext i; simp [slotSuffix]
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [residual, append, hp, hs]

end TriangularSlots

theorem dist_append_same_right_le (x y : Fin D → ℝ) (z : Fin E → ℝ) :
    dist (Fin.append x z) (Fin.append y z) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using dist_le_pi_dist x y j
  · simp

namespace PatchKernel

theorem freeze_value_dist_le (Φ : PatchKernel (D + E)) (x y : Fin D → ℝ)
    (z : Fin E → ℝ) :
    dist ((Φ.freeze x).value z) ((Φ.freeze y).value z) ≤ Φ.lip * dist x y :=
  (Φ.lipschitz.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (dist_append_same_right_le x y z) Φ.lip.coe_nonneg)

end PatchKernel

end Erdos3

end

section

namespace Erdos3

namespace TriangularSlots

variable {D E : ℕ}

theorem patchValue_freeze_dist_le (A : TriangularSlots E) (Φ : PatchKernel (D + E))
    (x y : Fin D → ℝ) :
    dist (A.patchValue (Φ.freeze x)) (A.patchValue (Φ.freeze y)) ≤ Φ.lip * dist x y :=
  A.patchValue_dist_le _ _ (mul_nonneg Φ.lip.coe_nonneg dist_nonneg)
    (Φ.freeze_value_dist_le x y)

theorem contributing_prefix_eq (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3)
    {v : Fin (D + E) → ℤ} (hv : Φ.value ((A.append B).residual v) ≠ 0) :
    slotPrefix v = b := by
  have hr := A.append_residual B (slotPrefix v) (slotSuffix v)
  rw [append_slotPrefix_slotSuffix] at hr
  have hp : ∀ i, |A.residual (slotPrefix v) i| ≤ 1 / 4 := by
    intro i
    have h := Φ.support _ hv (i.castAdd E)
    simpa only [hr, Fin.append_left] using h
  exact A.integer_unique (by norm_num) hp hb

theorem patchValue_append_eq (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3) :
    (A.append B).patchValue Φ =
      (B (fun i => (b i : ℝ))).patchValue (Φ.freeze (A.residual b)) := by
  by_cases h : ∃ v : Fin (D + E) → ℤ, Φ.value ((A.append B).residual v) ≠ 0
  · obtain ⟨v, hv⟩ := h
    have hp := A.contributing_prefix_eq B Φ b hb hv
    have hvform : Fin.append b (slotSuffix v) = v := by
      rw [← hp, append_slotPrefix_slotSuffix]
    have heq : Φ.value ((A.append B).residual v) =
        (Φ.freeze (A.residual b)).value ((B (fun i => (b i : ℝ))).residual (slotSuffix v)) := by
      rw [← hvform, A.append_residual]
      simp only [slotSuffix_append]
      rfl
    rw [(A.append B).patchValue_eq_of_nonzero Φ hv,
      (B (fun i => (b i : ℝ))).patchValue_eq_of_nonzero _ (by rwa [← heq]), heq]
  · have hz : ∀ v, Φ.value ((A.append B).residual v) = 0 := by simpa using h
    have ht : ∀ c, (Φ.freeze (A.residual b)).value
        ((B (fun i => (b i : ℝ))).residual c) = 0 := by
      intro c
      have heq := hz (Fin.append b c)
      simpa only [A.append_residual, PatchKernel.freeze] using heq
    rw [(A.append B).patchValue_eq_zero Φ hz,
      (B (fun i => (b i : ℝ))).patchValue_eq_zero _ ht]

theorem patchValue_freeze_prefix (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (z : Fin D → ℝ) {ε : ℝ}
    (hz : ∀ i, |z i| ≤ 1 / 4) (hε : ε < 1 / 12)
    (hclose : dist (A.residual b) z ≤ ε) :
    dist ((A.append B).patchValue Φ)
      ((B (fun i => (b i : ℝ))).patchValue (Φ.freeze z)) ≤ Φ.lip * ε := by
  have hb : ∀ i, |A.residual b i| ≤ 1 / 3 := by
    intro i
    have hcoord := (dist_le_pi_dist (A.residual b) z i).trans hclose
    rw [Real.dist_eq] at hcoord
    have htriangle : |A.residual b i| ≤ |A.residual b i - z i| + |z i| := by
      simpa only [sub_add_cancel] using abs_add_le (A.residual b i - z i) (z i)
    linarith [hz i]
  rw [A.patchValue_append_eq B Φ b hb]
  exact (patchValue_freeze_dist_le _ Φ _ _).trans
    (mul_le_mul_of_nonneg_left hclose Φ.lip.coe_nonneg)

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

theorem append_take_drop (A : TriangularSlots (D + E)) :
    A.takePrefix.append A.dropPrefix = A := by
  apply ext
  intro x i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [append, takePrefix, Fin.append_left]
    apply A.lower
    intro k
    refine Fin.addCases (fun l hk => ?_) (fun l hk => ?_) k
    · simp [slotPrefix]
    · have hbad : D + l.val < j.val := by simpa only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] using hk
      omega
  · simp only [append, dropPrefix, Fin.append_right, append_slotPrefix_slotSuffix]

theorem takePrefix_residual (A : TriangularSlots (D + E)) (v : Fin (D + E) → ℤ) :
    A.takePrefix.residual (slotPrefix v) = slotPrefix (A.residual v) := by
  have h := A.takePrefix.append_residual A.dropPrefix (slotPrefix v) (slotSuffix v)
  rw [append_take_drop, append_slotPrefix_slotSuffix] at h
  have hp := congrArg slotPrefix h
  simpa only [slotPrefix_append] using hp.symm

end Erdos3.TriangularSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLowestLayer
namespace OAI

section

namespace Erdos3

namespace TriangularSlots

variable {D : ℕ}

theorem affineBlock_residual (M : Matrix (Fin D) (Fin D) ℝ)
    (hM : ∀ i j, i ≤ j → M i j = 0) (P : Fin D → ℝ) (b : Fin D → ℤ) :
    (affineBlock M hM P).residual b = (1 - M).mulVec ((fun i => (b i : ℝ)) - P) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp only [residual, affineBlock, Pi.sub_apply, Pi.add_apply]
  ring

end TriangularSlots

theorem affine_residual_shift_identity {T : Type*} {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (P : T → Fin D → ℝ) (I : T → Fin D → ℤ) (t₀ t : T) (b₀ : Fin D → ℤ) :
    (TriangularSlots.affineBlock M hM (P t)).residual (shiftedIntegerBlock I t₀ b₀ t) -
      (TriangularSlots.affineBlock M hM (P t₀)).residual b₀ =
    -(1 - M).mulVec ((P t - fun i => (I t i : ℝ)) - (P t₀ - fun i => (I t₀ i : ℝ))) := by
  rw [TriangularSlots.affineBlock_residual, TriangularSlots.affineBlock_residual,
    ← Matrix.mulVec_sub, ← Matrix.mulVec_neg]
  congr 1
  ext i
  simp only [shiftedIntegerBlock, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Int.cast_sub, Int.cast_add]
  ring

theorem affine_residual_shift_dist {T : Type*} {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (P : T → Fin D → ℝ) (I : T → Fin D → ℤ) (t₀ t : T) (b₀ : Fin D → ℤ) :
    dist ((TriangularSlots.affineBlock M hM (P t)).residual (shiftedIntegerBlock I t₀ b₀ t))
      ((TriangularSlots.affineBlock M hM (P t₀)).residual b₀) =
    ‖(1 - M).mulVec ((P t - fun i => (I t i : ℝ)) - (P t₀ - fun i => (I t₀ i : ℝ)))‖ := by
  rw [dist_eq_norm, affine_residual_shift_identity, norm_neg]

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

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

theorem freezePrefix_center_eval {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (t : σ → ℝ) (x : Fin E → ℝ) (i : Fin E) :
    ((A.freezePrefix I hI).slots t).center x i =
      (A.slots t).center (Fin.append (fun j => aeval t (I j)) x) (i.natAdd D) := by
  simp only [slots, freezePrefix, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f : σ ⊕ Fin (D + i.val) → ℝ => aeval f (A.center (i.natAdd D)))
  funext v
  cases v with
  | inl a => simp [prefixSubstitution]
  | inr j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_left]
      change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (aeval (fun a => (X (Sum.inl a) : MvPolynomial (σ ⊕ Fin i.val) ℝ)) (I k)) =
        Fin.append (fun j => aeval t (I j)) x (k.castAdd E)
      rw [MvPolynomial.comp_aeval_apply, Fin.append_left]
      simp only [aeval_X, Sum.elim_inl]
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_right]
      change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (X (Sum.inr k) : MvPolynomial (σ ⊕ Fin i.val) ℝ) =
        Fin.append (fun j => aeval t (I j)) x ((earlierSlot i k).natAdd D)
      simp only [aeval_X, Sum.elim_inr, Fin.append_right]

end PolynomialSlots

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

theorem slots_freezePrefix {σ : Type*} {D E : ℕ} {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (t : σ → ℝ) :
    (A.freezePrefix I hI).slots t = (A.slots t).dropPrefix (fun j => aeval t (I j)) := by
  apply TriangularSlots.ext
  intro x i
  exact A.freezePrefix_center_eval I hI t x i

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

theorem value_rank_zero (A : PolynomialPatch σ s 0) (t : σ → ℝ) :
    A.value t = A.kernel.value 0 := by
  have h := (A.form.slots t).patchValue_eq_at_residual A.kernel
    (b := 0) (fun i => Fin.elim0 i)
  have hr : (A.form.slots t).residual 0 = 0 := Subsingleton.elim _ _
  simpa only [value, hr] using h

theorem freezePrefix_value (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) (t : σ → ℝ) :
    (A.freezePrefix I (by exact hI) z).value t =
      ((A.form.slots t).dropPrefix (fun j => aeval t (I j))).patchValue (A.kernel.freeze z) := by
  change ((A.form.freezePrefix I hI).slots t).patchValue _ = _
  rw [PolynomialSlots.slots_freezePrefix]
  rfl

theorem freezePrefix_error (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) (t : σ → ℝ) (b : Fin D → ℤ) {ε : ℝ}
    (hint : ∀ j, aeval t (I j) = (b j : ℝ))
    (hz : ∀ i, |z i| ≤ 1 / 4) (hε : ε < 1 / 12)
    (hclose : dist ((A.form.slots t).takePrefix.residual b) z ≤ ε) :
    dist (A.value t) ((A.freezePrefix I hI z).value t) ≤ A.kernel.lip * ε := by
  have h := (A.form.slots t).takePrefix.patchValue_freeze_prefix
    (A.form.slots t).dropPrefix A.kernel b z hz hε hclose
  rw [TriangularSlots.append_take_drop] at h
  rw [freezePrefix_value, show (fun j => aeval t (I j)) = (fun j => (b j : ℝ)) from funext hint]
  exact h

end PolynomialPatch

theorem shiftedParameterPolynomials_degree {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ : σ → ℝ) (b₀ : Fin D → ℤ)
    (w : Fin D → ℕ)
    (hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) :
    ∀ i, shiftedParameterPolynomials I t₀ b₀ i ∈ weightedSupportLE (fun _ : σ => 1) (w i) := by
  intro i
  exact (weightedSupportLE _ _).sub_mem
    ((weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _) (hI i))
    (weightedSupportLE_C _ _ _)

theorem shiftedParameterPolynomials_eval {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ t : σ → ℝ) (b₀ : Fin D → ℤ) :
    ∀ i, aeval t (shiftedParameterPolynomials I t₀ b₀ i) =
      (b₀ i : ℝ) + aeval t (I i) - aeval t₀ (I i) := by
  intro i
  simp only [shiftedParameterPolynomials, map_add, map_sub, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply]

namespace PolynomialPatch

theorem exists_freeze_affine_layer {σ : Type*} {s D E : ℕ}
    (A : PolynomialPatch σ s (D + E))
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (U : Set (σ → ℝ)) (P : (σ → ℝ) → Fin D → ℝ)
    (I : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (hint : ∀ t ∈ U, ∀ j, aeval t (I j) = (v t j : ℝ))
    (hhead : ∀ t ∈ U, (A.form.slots t).takePrefix = TriangularSlots.affineBlock M hM (P t))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(1 - M).mulVec
      ((P t - fun j => aeval t (I j)) - (P t₀ - fun j => aeval t₀ (I j)))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ε := by
  let b₀ := slotPrefix bref
  let z := (A.form.slots t₀).takePrefix.residual b₀
  let J := shiftedParameterPolynomials I t₀ b₀
  have hJ : ∀ j, J j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)) :=
    shiftedParameterPolynomials_degree I t₀ b₀ _ hI
  refine ⟨A.freezePrefix J hJ z, rfl, (fun _ => rfl), ?_⟩
  have hz : ∀ i, |z i| ≤ 1 / 4 := by
    intro i
    have h := A.kernel.support _ href (i.castAdd E)
    simpa only [z, b₀, TriangularSlots.takePrefix_residual, slotPrefix] using h
  intro t ht
  have hJvalue : ∀ j, aeval t (J j) = (shiftedIntegerBlock v t₀ b₀ t j : ℝ) := by
    intro j
    simp only [J, shiftedParameterPolynomials_eval, hint t ht, hint t₀ ht₀,
      shiftedIntegerBlock, Pi.add_apply, Pi.sub_apply, Int.cast_sub, Int.cast_add]
  apply A.freezePrefix_error J hJ z t (shiftedIntegerBlock v t₀ b₀ t) hJvalue hz hε
  change dist ((A.form.slots t).takePrefix.residual (shiftedIntegerBlock v t₀ b₀ t))
    ((A.form.slots t₀).takePrefix.residual b₀) ≤ ε
  rw [hhead t ht, hhead t₀ ht₀, affine_residual_shift_dist]
  simpa only [hint t ht, hint t₀ ht₀] using hosc t ht

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

theorem onAffineLine_value (A : PolynomialPatch σ s d) (a q : σ → ℝ) (n : ℝ) :
    (A.onAffineLine a q).value (fun _ => n) = A.value (fun i => a i + q i * n) := by
  rw [onAffineLine, reparam_value]
  congr 1
  funext i
  simp [affineLineParameters]

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

@[simp] theorem constant_value (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : σ → ℝ) :
    (constant σ s c hc).value t = c := by
  exact ((constant σ s c hc).form.slots t).patchValue_eq_at_residual (constant σ s c hc).kernel
    (b := 0) (fun i => Fin.elim0 i)

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MonotoneWeightLayer
namespace OAI

section

namespace Erdos3

theorem monotone_weight_layer {d h : ℕ} (w : Fin d → ℕ)
    (hmono : Monotone w) (hmin : ∀ i, h ≤ w i) :
    ∃ D ≤ d, (∀ i : Fin d, i.val < D → w i = h) ∧
      ∀ i : Fin d, D ≤ i.val → h + 1 ≤ w i := by
  classical
  let test := fun n : ℕ => d ≤ n ∨ ∃ hn : n < d, h < w ⟨n, hn⟩
  have hex : ∃ n, test n := ⟨d, Or.inl le_rfl⟩
  let D := Nat.find hex
  have hD : D ≤ d := Nat.find_le (Or.inl le_rfl : test d)
  refine ⟨D, hD, ?_, ?_⟩
  · intro i hi
    have hn := Nat.find_min hex hi
    have hle : w i ≤ h := by
      by_contra hnle
      exact hn (Or.inr ⟨i.isLt, lt_of_not_ge hnle⟩)
    exact le_antisymm hle (hmin i)
  · intro i hi
    have hs : test D := Nat.find_spec hex
    rcases hs with hs | ⟨hDd, hs⟩
    · omega
    · have hwi := hmono (show (⟨D, hDd⟩ : Fin d) ≤ i from hi)
      omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenPartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_cell_score {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (cell : Ω → ι) (g : Ω → ℝ) {σ τ L : ℝ} (hL : 0 ≤ L) (hτ : 0 ≤ τ)
    (hg : ∀ x, g x ≤ 1) (hscore : σ ≤ 𝔼 x, g x)
    (hbudget : (Fintype.card ι : ℝ) * L / Fintype.card Ω + τ < σ) :
    ∃ i, L ≤ ((partitionCell cell i).card : ℝ) ∧ τ < 𝔼 x ∈ partitionCell cell i, g x := by
  classical
  by_contra! hnone
  have hcell (i : ι) : (∑ x ∈ partitionCell cell i, g x) ≤ L + τ * (partitionCell cell i).card := by
    by_cases hlarge : L ≤ ((partitionCell cell i).card : ℝ)
    · have h := mul_le_mul_of_nonneg_left (hnone i hlarge) (Nat.cast_nonneg (partitionCell cell i).card : (0 : ℝ) ≤ _)
      rw [Finset.card_mul_expect] at h
      nlinarith
    · have hsum : (∑ x ∈ partitionCell cell i, g x) ≤ ((partitionCell cell i).card : ℝ) := by
        calc
          _ ≤ ∑ x ∈ partitionCell cell i, (1 : ℝ) := Finset.sum_le_sum fun x _ => hg x
          _ = _ := by simp
      have hnonneg := mul_nonneg hτ (Nat.cast_nonneg (partitionCell cell i).card : (0 : ℝ) ≤ _)
      linarith
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hcell i)
  rw [sum_partitionCell, Finset.sum_add_distrib, ← Finset.mul_sum, card_partitionCell_sum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hscore' := (le_div_iff₀ hN).mp (show σ ≤ (∑ x, g x) / Fintype.card Ω by
    simpa only [Fintype.expect_eq_sum_div_card] using hscore)
  have hbudget' := mul_lt_mul_of_pos_right hbudget hN
  rw [add_mul, div_mul_cancel₀ _ hN.ne'] at hbudget'
  nlinarith

theorem weighted_score_le_of_close {f b B C ε : ℝ}
    (hf : f ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hclose : dist B C ≤ ε) : (f - b) * B ≤ (f - b) * C + ε := by
  have hf' : |f - b| ≤ 1 := abs_le.mpr ⟨by linarith [hf.1, hb.2], by linarith [hf.2, hb.1]⟩
  have hdiff : (f - b) * (B - C) ≤ ε := by
    calc
      _ ≤ |(f - b) * (B - C)| := le_abs_self _
      _ = |f - b| * |B - C| := abs_mul _ _
      _ ≤ 1 * ε := mul_le_mul hf' (by simpa only [Real.dist_eq] using hclose) (abs_nonneg _) (by norm_num)
      _ = ε := one_mul _
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

theorem expect_cell (i : P.Label) (f : ℕ → ℝ) :
    (𝔼 n ∈ partitionCell P.cell i, f n.val) =
      𝔼 j : Fin (P.length i), f (P.start i + P.step i * j.val) := by
  classical
  have he := Fintype.expect_equiv (P.pointEquiv i)
    (fun j => f (P.start i + P.step i * j.val)) (fun n => f n.val.val)
    (fun j => by simp [pointEquiv, point, P.equiv_val])
  have hcoe : (𝔼 n : ↥(partitionCell P.cell i), f n.val.val) =
      𝔼 n ∈ partitionCell P.cell i, f n.val := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
    rw [Finset.sum_coe_sort (partitionCell P.cell i) (fun n : Fin N => f n.val)]
  exact hcoe.symm.trans he.symm

end FiniteProgressionPartition
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

universe u

open Polynomial

theorem polynomialCoordinatePartitionBound_zero : PolynomialCoordinatePartitionBound.{u} 0 1 1 := by
  intro ι _ P hP N H hH hscale hsize
  have hHN : H ≤ N := by simpa using hsize
  refine ⟨FiniteProgressionPartition.whole N, (fun _ j => (P j).coeff 0), (fun _ _ _ => 0), ?_, ?_⟩
  · have hcard : Fintype.card (FiniteProgressionPartition.whole N).Label = 1 := by
      let : Unique (FiniteProgressionPartition.whole N).Label := inferInstanceAs (Unique Unit)
      exact Fintype.card_unique
    rw [hcard]
    simpa using hHN
  · intro i n hn j
    have heq (x : ℝ) : (P j).eval x = (P j).coeff 0 := by
      simpa only [eval_C] using congrArg (fun Q : Polynomial ℝ => Q.eval x)
        (eq_C_of_natDegree_le_zero (hP j))
    rw [heq]
    simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UniformCoordinatePartition
namespace OAI

section

namespace Erdos3

universe u

theorem PolynomialCoordinatePartitionBound.mono {h p p' : ℕ} {K K' : ℝ}
    (hpartition : PolynomialCoordinatePartitionBound.{u} h K p)
    (hK : K ≤ K') (hp : p ≤ p') : PolynomialCoordinatePartitionBound.{u} h K' p' := by
  intro ι _ P hP N H hH hscale hsize
  apply hpartition ι P hP N H hH
  · exact (mul_le_mul_of_nonneg_right hK (by positivity)).trans hscale
  · exact (Nat.pow_le_pow_right hH (Nat.mul_le_mul_right _ hp)).trans hsize

theorem exists_uniform_coordinate_partition_bound (s : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ h ≤ s, PolynomialCoordinatePartitionBound.{u} h K p := by
  induction s with
  | zero =>
    refine ⟨1, 1, le_rfl, by omega, ?_⟩
    intro h hh
    have heq : h = 0 := by omega
    subst h
    exact polynomialCoordinatePartitionBound_zero
  | succ s ih =>
    obtain ⟨K, p, hK, hp, hpart⟩ := ih
    obtain ⟨K', p', hK', hp', hpart'⟩ := exists_polynomial_coordinate_partition_bound_s2.{u} (s + 1)
    refine ⟨max K K', p + p', hK.trans (le_max_left _ _), by omega, ?_⟩
    intro h hh
    by_cases hs : h ≤ s
    · exact (hpart h hs).mono (le_max_left _ _) (by omega)
    · have heq : h = s + 1 := by omega
      subst h
      exact hpart'.mono (le_max_right _ _) (by omega)

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

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

namespace PolynomialPatch

variable {σ : Type*} {s D E h : ℕ}

theorem LowestLayerModel.exists_freeze (A : PolynomialPatch σ s (D + E))
    (L : A.LowestLayerModel h) (U : Set (σ → ℝ))
    (I : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hint : ∀ t ∈ U, ∀ i, aeval t (I i) = (v t i : ℝ))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(1 - L.matrix).mulVec
      ((fun i => aeval t (L.origin i) - aeval t (I i)) -
        (fun i => aeval t₀ (L.origin i) - aeval t₀ (I i)))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ε := by
  apply A.exists_freeze_affine_layer L.matrix L.strict U
    (fun t i => aeval t (L.origin i)) I v
    (fun i => by rw [L.weights i]; exact hI i) hint
    (fun t _ => L.form_eq t) t₀ ht₀ bref href hε
  exact hosc

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TriangularAffineReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d : ℕ}

theorem earlierSlotMatrix_apply_lt {R : Type*} [CommRing R]
    (m : (i : Fin d) → Fin i.val → R) (i j : Fin d) (hji : j < i) :
    earlierSlotMatrix m i j = m i ⟨j.val, hji⟩ := by
  classical
  unfold earlierSlotMatrix
  rw [Finset.sum_eq_single (⟨j.val, hji⟩ : Fin i.val)]
  · simp [earlierSlot]
  · intro k _ hk
    apply if_neg
    intro heq
    apply hk
    exact Fin.ext (congrArg (fun t : Fin d => t.val) heq)
  · simp

theorem unitLower_mulVec {R : Type*} [CommRing R]
    (T : Matrix (Fin d) (Fin d) R) (htri : T.IsLowerTriangular)
    (hdiag : ∀ i, T i i = 1) (v : Fin d → R) (i : Fin d) :
    T.mulVec v i = v i + ∑ k : Fin i.val, T i (earlierSlot i k) * v (earlierSlot i k) := by
  classical
  have hT : T = 1 + earlierSlotMatrix (fun i k => T i (earlierSlot i k)) := by
    ext a b
    by_cases hba : b < a
    · rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne.symm,
        earlierSlotMatrix_apply_lt _ a b hba, zero_add]
      rfl
    · rw [Matrix.add_apply, earlierSlotMatrix_strict _ a b (le_of_not_gt hba), add_zero]
      by_cases hab : a = b
      · subst b
        simp [hdiag]
      · have hablt : a < b := lt_of_le_of_ne (le_of_not_gt hba) hab
        rw [htri hablt, Matrix.one_apply_ne hab]
  conv_lhs =>
    rw [hT, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, earlierSlotMatrix_mulVec]

theorem triangularReductionMatrix_above (T : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) (hij : i < j) : triangularReductionMatrix T i j = 0 := by
  unfold triangularReductionMatrix
  rw [reducedLatticeColumn]
  simp only [if_pos hij]

theorem triangularReductionMatrix_diag (T : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : triangularReductionMatrix T i i = 1 := by
  unfold triangularReductionMatrix
  rw [reducedLatticeColumn]
  simp

theorem triangularReductionMatrix_det (T : Matrix (Fin d) (Fin d) ℝ) :
    (triangularReductionMatrix T).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (triangularReductionMatrix_above T)]
  exact Finset.prod_eq_one (fun i _ => triangularReductionMatrix_diag T i)

theorem reducedTriangularMatrix_entry (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d) :
    reducedTriangularMatrix T i j = (triangularReductionMatrix T i j : ℝ) +
      ∑ k : Fin i.val, T i (earlierSlot i k) *
        (triangularReductionMatrix T (earlierSlot i k) j : ℝ) := by
  exact unitLower_mulVec T htri hdiag (fun k => (triangularReductionMatrix T k j : ℝ)) i

theorem reducedTriangularMatrix_above (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d)
    (hij : i < j) : reducedTriangularMatrix T i j = 0 := by
  rw [reducedTriangularMatrix_entry T htri hdiag,
    triangularReductionMatrix_above T i j hij, Int.cast_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  rw [triangularReductionMatrix_above T (earlierSlot i k) j
    (lt_trans (show earlierSlot i k < i from k.isLt) hij), Int.cast_zero, mul_zero]

theorem reducedTriangularMatrix_diag (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i : Fin d) :
    reducedTriangularMatrix T i i = 1 := by
  rw [reducedTriangularMatrix_entry T htri hdiag, triangularReductionMatrix_diag,
    Int.cast_one]
  have hz : (∑ k : Fin i.val, T i (earlierSlot i k) *
      (triangularReductionMatrix T (earlierSlot i k) i : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [triangularReductionMatrix_above T (earlierSlot i k) i k.isLt,
      Int.cast_zero, mul_zero]
  rw [hz, add_zero]

theorem reducedTriangularMatrix_lower_bound (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d)
    (hji : j < i) : |reducedTriangularMatrix T i j| ≤ 1 / 2 := by
  rw [reducedTriangularMatrix_entry T htri hdiag]
  have hu : triangularReductionMatrix T i j =
      -round (∑ k : Fin i.val, T i (earlierSlot i k) *
        (triangularReductionMatrix T (earlierSlot i k) j : ℝ)) := by
    unfold triangularReductionMatrix
    rw [reducedLatticeColumn]
    simp only [if_neg (not_lt_of_ge hji.le), if_neg hji.ne.symm]
  rw [hu, Int.cast_neg, neg_add_eq_sub]
  exact abs_sub_round _

theorem reducedTriangularMatrix_bound (T : Matrix (Fin d) (Fin d) ℝ)
    (htri : T.IsLowerTriangular) (hdiag : ∀ i, T i i = 1) (i j : Fin d) :
    |reducedTriangularMatrix T i j| ≤ 1 := by
  rcases lt_trichotomy i j with h | h | h
  · simp [reducedTriangularMatrix_above T htri hdiag i j h]
  · subst j
    simp [reducedTriangularMatrix_diag T htri hdiag]
  · exact (reducedTriangularMatrix_lower_bound T htri hdiag i j h).trans (by norm_num)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

theorem bounded_matrix_mulVec_lipschitz (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : ∀ i j, |T i j| ≤ 1) : LipschitzWith (d : ℝ≥0) T.mulVec := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (T.mulVec x) (T.mulVec y) ≤ (d : ℝ) * dist x y
  apply (dist_pi_le_iff (mul_nonneg (Nat.cast_nonneg d) dist_nonneg)).mpr
  intro i
  simp only [Real.dist_eq, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |T i j * x j - T i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, dist x y := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul]
      have hj : |x j - y j| ≤ dist x y := by
        simpa only [Real.dist_eq] using dist_le_pi_dist x y j
      exact (mul_le_mul (hT i j) hj (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (d : ℝ) * dist x y := by simp

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

theorem integerMatrix_cast_mul_inv (U : Matrix (Fin d) (Fin d) ℤ)
    (hU : IsUnit U.det) :
    U.map (Int.castRingHom ℝ) * U⁻¹.map (Int.castRingHom ℝ) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv U hU]
  exact Matrix.map_one _ (map_zero (Int.castRingHom ℝ)) (map_one (Int.castRingHom ℝ))

theorem real_basis_change_residual (T : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U.det) (x y : Fin d → ℝ) :
    T.mulVec (x - (U.map (Int.castRingHom ℝ)).mulVec y) =
      (T * U.map (Int.castRingHom ℝ)).mulVec
        ((U⁻¹.map (Int.castRingHom ℝ)).mulVec x - y) := by
  conv_rhs =>
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      integerMatrix_cast_mul_inv U hU, Matrix.one_mulVec]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDifferenceStability
namespace OAI

section

namespace Erdos3

open scoped fwdDiff

theorem norm_fwdDiff_iter_le_local {V : Type*} [SeminormedAddCommGroup V]
    (f : ℕ → V) (n x : ℕ) {ε : ℝ}
    (h : ∀ k ≤ n, ‖f (x + k)‖ ≤ ε) : ‖Δ_[1] ^[n] f x‖ ≤ (2 : ℝ) ^ n * ε := by
  induction n generalizing x with
  | zero => simpa using h 0 (by omega)
  | succ n ih =>
    have hleft : ‖Δ_[1] ^[n] f (x + 1)‖ ≤ (2 : ℝ) ^ n * ε := by
      apply ih
      intro k hk
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (k + 1) (by omega)
    have hright : ‖Δ_[1] ^[n] f x‖ ≤ (2 : ℝ) ^ n * ε :=
      ih x (fun k hk => h k (by omega))
    rw [Function.iterate_succ_apply']
    change ‖Δ_[1] ^[n] f (x + 1) - Δ_[1] ^[n] f x‖ ≤ _
    exact (norm_sub_le _ _).trans (by rw [pow_succ]; linarith)

theorem fwdDiff_iter_sub {V : Type*} [AddCommGroup V]
    (f g : ℕ → V) (n x : ℕ) :
    Δ_[1] ^[n] (fun k => f k - g k) x = Δ_[1] ^[n] f x - Δ_[1] ^[n] g x := by
  simp only [fwdDiff_iter_eq_sum_shift, smul_sub, Finset.sum_sub_distrib]

theorem fwdDiff_iter_intCast (g : ℕ → ℤ) (n x : ℕ) :
    Δ_[1] ^[n] (fun k => (g k : ℝ)) x = (Δ_[1] ^[n] g x : ℤ) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', fwdDiff, ih, Int.cast_sub]

theorem fwdDiff_iter_natCast (f : ℝ → ℝ) (n x : ℕ) :
    Δ_[1] ^[n] (fun k : ℕ => f k) x = Δ_[(1 : ℝ)] ^[n] f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', fwdDiff, ih, Nat.cast_add, Nat.cast_one]

theorem integer_fwdDiff_eq_zero_of_close (g : ℕ → ℤ) (f : ℕ → ℝ) (n x : ℕ)
    {ε : ℝ} (hsmall : (2 : ℝ) ^ n * ε < 1)
    (happrox : ∀ k ≤ n, ‖(g (x + k) : ℝ) - f (x + k)‖ ≤ ε)
    (hf : Δ_[1] ^[n] f x = 0) : Δ_[1] ^[n] g x = 0 := by
  have hbound := norm_fwdDiff_iter_le_local (fun k => (g k : ℝ) - f k) n x happrox
  rw [fwdDiff_iter_sub, fwdDiff_iter_intCast, hf, sub_zero] at hbound
  have habs : |((Δ_[1] ^[n] g x : ℤ) : ℝ)| < 1 := by
    simpa only [Real.norm_eq_abs] using hbound.trans_lt hsmall
  have hleft : (-1 : ℤ) < Δ_[1] ^[n] g x := by exact_mod_cast (abs_lt.mp habs).1
  have hright : Δ_[1] ^[n] g x < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  omega

theorem integer_polynomial_lift_differences (P : Polynomial ℝ) (g : ℕ → ℤ)
    {s N : ℕ} {ε : ℝ} (hdegree : P.natDegree ≤ s)
    (hsmall : (2 : ℝ) ^ (s + 1) * ε < 1)
    (happrox : ∀ n < N, ‖(g n : ℝ) - P.eval (n : ℝ)‖ ≤ ε) :
    ∀ x, x + s + 1 < N → Δ_[1] ^[s + 1] g x = 0 := by
  intro x hx
  apply integer_fwdDiff_eq_zero_of_close g (fun n => P.eval n) (s + 1) x hsmall
  · intro k hk
    exact happrox (x + k) (by omega)
  · rw [fwdDiff_iter_natCast P.eval]
    have hzero := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := P) (by omega : P.natDegree < s + 1)
    exact congrFun hzero (x : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SingleParameterPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators fwdDiff

theorem fwdDiff_iter_eq_zero_of_local {V : Type*} [AddCommGroup V]
    (g : ℕ → V) {d N : ℕ}
    (hzero : ∀ x, x + d < N → (fwdDiff 1)^[d] g x = 0)
    (k : ℕ) (hk : d ≤ k) : ∀ x, x + k < N → (fwdDiff 1)^[k] g x = 0 := by
  induction k, hk using Nat.le_induction with
  | base => exact hzero
  | succ k hk ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    change (fwdDiff 1)^[k] g (x + 1) - (fwdDiff 1)^[k] g x = 0
    rw [ih (x + 1) (by omega), ih x (by omega), sub_self]

theorem finite_interval_newton_formula (g : ℕ → ℤ) {s N : ℕ}
    (hzero : ∀ x, x + s + 1 < N → (fwdDiff 1)^[s + 1] g x = 0)
    (n : ℕ) (hn : n < N) :
    g n = ∑ k ∈ Finset.range (s + 1), (n.choose k : ℤ) * (fwdDiff 1)^[k] g 0 := by
  have hnewton := shift_eq_sum_fwdDiff_iter 1 g n 0
  simp only [nsmul_eq_mul, Nat.cast_id, mul_one, zero_add] at hnewton
  rw [hnewton]
  by_cases hns : n ≤ s
  · apply Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ s + 1))
    intro k _ hk
    have hnk : n < k := by simp only [Finset.mem_range] at hk; omega
    simp [Nat.choose_eq_zero_of_lt hnk]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : s + 1 ≤ n + 1))
    intro k hk hks
    have hsk : s + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hks
    have hkN : 0 + k < N := by have := Finset.mem_range.mp hk; omega
    have hz := fwdDiff_iter_eq_zero_of_local g (d := s + 1)
      (fun x hx => hzero x (by omega)) k hsk 0 hkN
    simp [hz]

theorem integerNewtonPolynomial_natDegree_le (s : ℕ) (c : ℕ → ℤ) :
    (integerNewtonPolynomial s c).natDegree ≤ s := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [descPochhammer_natDegree]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

theorem integerNewtonPolynomial_eval_nat (s n : ℕ) (c : ℕ → ℤ) :
    (integerNewtonPolynomial s c).eval (n : ℝ) =
      ((∑ k ∈ Finset.range (s + 1), (n.choose k : ℤ) * c k : ℤ) : ℝ) := by
  simp only [integerNewtonPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.cast_choose_eq_descPochhammer_div (K := ℝ)]
  ring

theorem integerNewtonPolynomial_integer_valued (s n : ℕ) (c : ℕ → ℤ) :
    ∃ z : ℤ, (integerNewtonPolynomial s c).eval (n : ℝ) = z :=
  ⟨_, integerNewtonPolynomial_eval_nat s n c⟩

theorem exists_integer_polynomial_of_local_differences (g : ℕ → ℤ) {s N : ℕ}
    (hzero : ∀ x, x + s + 1 < N → (fwdDiff 1)^[s + 1] g x = 0) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ s ∧
      (∀ n : ℕ, ∃ z : ℤ, Q.eval (n : ℝ) = z) ∧
      ∀ n < N, Q.eval (n : ℝ) = (g n : ℝ) := by
  refine ⟨integerNewtonPolynomial s (fun index => (fwdDiff 1)^[index] g 0),
    integerNewtonPolynomial_natDegree_le _ _,
    fun n => integerNewtonPolynomial_integer_valued _ n _, ?_⟩
  intro n hn
  rw [integerNewtonPolynomial_eval_nat, ← finite_interval_newton_formula g hzero n hn]

theorem exists_integer_polynomial_lift (P : Polynomial ℝ) (g : ℕ → ℤ)
    {s N : ℕ} {ε : ℝ} (hdegree : P.natDegree ≤ s)
    (hsmall : (2 : ℝ) ^ (s + 1) * ε < 1)
    (happrox : ∀ n < N, ‖(g n : ℝ) - P.eval (n : ℝ)‖ ≤ ε) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ s ∧
      (∀ n : ℕ, ∃ z : ℤ, Q.eval (n : ℝ) = z) ∧
      (∀ n < N, Q.eval (n : ℝ) = (g n : ℝ)) ∧
      ∀ n < N, ‖Q.eval (n : ℝ) - P.eval (n : ℝ)‖ ≤ ε := by
  obtain ⟨Q, hdeg, hint, heq⟩ := exists_integer_polynomial_of_local_differences g
    (integer_polynomial_lift_differences P g hdegree hsmall happrox)
  refine ⟨Q, hdeg, hint, heq, ?_⟩
  intro n hn
  rw [heq n hn]
  exact happrox n hn

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [Unique σ] [CommRing R]

theorem singleParameter_natDegree_le {p : MvPolynomial σ R} {h : ℕ}
    (hp : p ∈ weightedSupportLE (fun _ : σ => 1) h) :
    (uniqueAlgEquiv R σ p).natDegree ≤ h := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_uniqueAlgEquiv]
  by_contra hne
  have hbound := hp (mem_support_iff.mpr hne)
  change Finsupp.weight (fun _ : σ => 1) (Finsupp.single default n) ≤ h at hbound
  simp only [Finsupp.weight_single, smul_eq_mul, mul_one] at hbound
  omega

theorem singleParameter_symm_degree {p : Polynomial R} {h : ℕ}
    (hp : p.natDegree ≤ h) :
    (uniqueAlgEquiv R σ).symm p ∈ weightedSupportLE (fun _ : σ => 1) h := by
  intro α hα
  have hne := mem_support_iff.mp hα
  change ((uniqueAlgEquiv R σ).symm p).coeff α ≠ 0 at hne
  rw [coeff_uniqueAlgEquiv_symm] at hne
  have hbound := (Polynomial.le_natDegree_of_ne_zero hne).trans hp
  change Finsupp.weight (fun _ : σ => 1) α ≤ h
  rw [Finsupp.unique_single α, Finsupp.weight_single]
  simpa only [smul_eq_mul, mul_one] using hbound

theorem singleParameter_eval (p : MvPolynomial σ R) (x : R) :
    (uniqueAlgEquiv R σ p).eval x = aeval (fun _ : σ => x) p := by
  exact eval₂_const_uniqueAlgEquiv (φ := RingHom.id R)

theorem singleParameter_symm_eval (p : Polynomial R) (x : R) :
    aeval (fun _ : σ => x) ((uniqueAlgEquiv R σ).symm p) = p.eval x := by
  exact eval₂_const_uniqueAlgEquiv_symm (φ := RingHom.id R)

theorem exists_singleParameter_integer_lift (P : MvPolynomial σ ℝ) (g : ℕ → ℤ)
    {h N : ℕ} {ε : ℝ}
    (hdegree : P ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hsmall : (2 : ℝ) ^ (h + 1) * ε < 1)
    (happrox : ∀ n < N, ‖(g n : ℝ) - aeval (fun _ => (n : ℝ)) P‖ ≤ ε) :
    ∃ Q : MvPolynomial σ ℝ,
      Q ∈ weightedSupportLE (fun _ : σ => 1) h ∧
      (∀ n : ℕ, ∃ z : ℤ, aeval (fun _ => (n : ℝ)) Q = z) ∧
      (∀ n < N, aeval (fun _ => (n : ℝ)) Q = (g n : ℝ)) ∧
      ∀ n < N, ‖aeval (fun _ => (n : ℝ)) Q - aeval (fun _ => (n : ℝ)) P‖ ≤ ε := by
  obtain ⟨Q, hQ, hint, heq, hclose⟩ := exists_integer_polynomial_lift
    (uniqueAlgEquiv ℝ σ P) g (singleParameter_natDegree_le hdegree) hsmall
    (by simpa only [singleParameter_eval] using happrox)
  refine ⟨(uniqueAlgEquiv ℝ σ).symm Q, singleParameter_symm_degree hQ, ?_, ?_, ?_⟩
  · simpa only [singleParameter_symm_eval] using hint
  · simpa only [singleParameter_symm_eval] using heq
  · simpa only [singleParameter_symm_eval, singleParameter_eval] using hclose

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedLayerFreezing
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch.LowestLayerModel

variable {σ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}
    (L : A.LowestLayerModel h)

theorem residualMatrix_lower : (1 - L.matrix).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp [Matrix.sub_apply, Matrix.one_apply_ne hij.ne, L.strict i j hij.le]

theorem residualMatrix_diag (i : Fin D) : (1 - L.matrix) i i = 1 := by
  simp [Matrix.sub_apply, L.strict i i le_rfl]

theorem integerChange_det : L.integerChange.det = 1 :=
  triangularReductionMatrix_det (1 - L.matrix)

theorem normalizedOrigin_degree (i : Fin D) :
    L.normalizedOrigin i ∈ weightedSupportLE (fun _ : σ => 1) h :=
  polynomialMatrixAction_degree _ L.origin L.degree i

theorem normalizedOrigin_residual (t : σ → ℝ) (y : Fin D → ℝ) :
    (1 - L.matrix).mulVec ((fun i => aeval t (L.origin i)) -
      (L.integerChange.map (Int.castRingHom ℝ)).mulVec y) =
      (reducedTriangularMatrix (1 - L.matrix)).mulVec
        ((fun i => aeval t (L.normalizedOrigin i)) - y) := by
  have hU : IsUnit L.integerChange.det := by rw [L.integerChange_det]; exact isUnit_one
  simpa only [normalizedOrigin, polynomialMatrixAction_eval, integerChange,
    reducedTriangularMatrix] using real_basis_change_residual (1 - L.matrix)
      L.integerChange hU (fun i => aeval t (L.origin i)) y

theorem exists_freeze_normalized (U : Set (σ → ℝ))
    (J : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hJ : ∀ i, J i ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hint : ∀ t ∈ U, ∀ i, aeval t (J i) = (v t i : ℝ))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : (D : ℝ) * ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) -
      (fun i => aeval t₀ (L.normalizedOrigin i) - aeval t₀ (J i))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ((D : ℝ) * ε) := by
  let I := polynomialMatrixAction (L.integerChange.map (Int.castRingHom ℝ)) J
  let w (t : σ → ℝ) := L.integerChange.mulVec (v t)
  have hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) h :=
    polynomialMatrixAction_degree _ J hJ
  have hIeval : ∀ t ∈ U, ∀ i, aeval t (I i) = (w t i : ℝ) := by
    intro t ht i
    have heval := congrFun (polynomialMatrixAction_eval
      (L.integerChange.map (Int.castRingHom ℝ)) J t) i
    change aeval t (I i) = _ at heval
    rw [heval]
    simp only [hint t ht]
    exact (RingHom.map_mulVec (Int.castRingHom ℝ) L.integerChange (v t) i).symm
  have hres (t : σ → ℝ) :
      (1 - L.matrix).mulVec (fun i => aeval t (L.origin i) - aeval t (I i)) =
        (reducedTriangularMatrix (1 - L.matrix)).mulVec
          (fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) := by
    change (1 - L.matrix).mulVec ((fun i => aeval t (L.origin i)) -
      (fun i => aeval t (polynomialMatrixAction _ J i))) = _
    rw [polynomialMatrixAction_eval]
    exact L.normalizedOrigin_residual t (fun i => aeval t (J i))
  apply L.exists_freeze A U I w hI hIeval t₀ ht₀ bref href hε
  intro t ht
  rw [Matrix.mulVec_sub, hres t, hres t₀, ← dist_eq_norm]
  have hbound := (bounded_matrix_mulVec_lipschitz
    (reducedTriangularMatrix (1 - L.matrix))
    (reducedTriangularMatrix_bound (1 - L.matrix) L.residualMatrix_lower
      L.residualMatrix_diag)).dist_le_mul
        (fun i => aeval t (L.normalizedOrigin i) - aeval t (J i))
        (fun i => aeval t₀ (L.normalizedOrigin i) - aeval t₀ (J i))
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (by simpa only [dist_eq_norm] using hosc t ht) (Nat.cast_nonneg D))

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open _root_.MvPolynomial

variable {σ τ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}

theorem reparam_normalizedOrigin (L : A.LowestLayerModel h)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin D) :
    (L.reparam f hf).normalizedOrigin i = aeval f (L.normalizedOrigin i) := by
  simp [normalizedOrigin, polynomialMatrixAction, reparam, integerChange]

theorem onAffineLine_normalizedOrigin_eval (L : A.LowestLayerModel h)
    (a q : σ → ℝ) (n : ℝ) (i : Fin D) :
    aeval (fun _ : Unit => n) ((L.onAffineLine a q).normalizedOrigin i) =
      aeval (fun j => a j + q j * n) (L.normalizedOrigin i) := by
  change aeval (fun _ : Unit => n) ((L.reparam _ _).normalizedOrigin i) = _
  rw [reparam_normalizedOrigin, MvPolynomial.comp_aeval_apply]
  have hargs : (fun j => aeval (fun _ : Unit => n) (PolynomialPatch.affineLineParameters a q j)) =
      (fun j => a j + q j * n) := by
    funext j
    simp [PolynomialPatch.affineLineParameters, MvPolynomial.aeval_eq_eval]
  rw [hargs]

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace PolynomialPatch.LowestLayerModel

variable {s D E h : ℕ} {A : PolynomialPatch Unit s (D + E)}

theorem exists_freeze_normalized_cell_at (L : A.LowestLayerModel h)
    (g : ℕ → Fin D → ℤ) (z : Fin D → ℝ) {N n₀ : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : (2 : ℝ) ^ (h + 1) * δ < 1)
    (hfreeze : (D : ℝ) * (2 * δ) < 1 / 12)
    (hcell : ∀ n < N, ∀ i,
      ‖aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - g n i - z i‖ ≤ δ)
    (hn₀ : n₀ < N) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots (fun _ => (n₀ : ℝ))).residual bref) ≠ 0) :
    ∃ F : PolynomialPatch Unit s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ n < N, dist (A.value (fun _ => (n : ℝ))) (F.value (fun _ => (n : ℝ))) ≤
        A.kernel.lip * ((D : ℝ) * (2 * δ)) := by
  have hlift (i : Fin D) := exists_singleParameter_integer_lift
    (L.normalizedOrigin i - C (z i)) (fun n => g n i)
    ((weightedSupportLE _ _).sub_mem (L.normalizedOrigin_degree i)
      (weightedSupportLE_C _ _ _)) hsmall
    (show ∀ n < N, ‖(g n i : ℝ) - aeval (fun _ : Unit => (n : ℝ))
        (L.normalizedOrigin i - C (z i))‖ ≤ δ from by
      intro n hn
      simp only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (g n i : ℝ) - (aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - z i) =
        -(aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - g n i - z i) by ring,
        norm_neg]
      exact hcell n hn i)
  choose J hJ hJint hJeq hJclose using hlift
  let U : Set (Unit → ℝ) := {t | ∃ n < N, t = fun _ : Unit => (n : ℝ)}
  let v (t : Unit → ℝ) := g ⌊t ()⌋₊
  have hint : ∀ t ∈ U, ∀ i, aeval t (J i) = (v t i : ℝ) := by
    rintro t ⟨n, hn, rfl⟩ i
    simpa only [v, Nat.floor_natCast] using hJeq i n hn
  have hdist (n : ℕ) (hn : n < N) :
      dist (fun i => aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) -
        aeval (fun _ : Unit => (n : ℝ)) (J i)) z ≤ δ := by
    apply (dist_pi_le_iff hδ).mpr
    intro i
    rw [hJeq i n hn]
    simpa only [dist_eq_norm] using hcell n hn i
  have hosc : ∀ t ∈ U,
      ‖(fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) -
        (fun i => aeval (fun _ : Unit => (n₀ : ℝ)) (L.normalizedOrigin i) -
          aeval (fun _ : Unit => (n₀ : ℝ)) (J i))‖ ≤ 2 * δ := by
    rintro t ⟨n, hn, rfl⟩
    rw [← dist_eq_norm]
    calc
      _ ≤ dist (fun i => aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) -
            aeval (fun _ : Unit => (n : ℝ)) (J i)) z +
          dist z (fun i => aeval (fun _ : Unit => (n₀ : ℝ)) (L.normalizedOrigin i) -
            aeval (fun _ : Unit => (n₀ : ℝ)) (J i)) := dist_triangle _ _ _
      _ ≤ δ + δ := add_le_add (hdist n hn) (by simpa only [dist_comm] using hdist n₀ hn₀)
      _ = 2 * δ := by ring
  obtain ⟨F, hF, hweights, herror⟩ := L.exists_freeze_normalized U J v hJ hint
    (fun _ => (n₀ : ℝ)) ⟨n₀, hn₀, rfl⟩ bref href hfreeze hosc
  exact ⟨F, hF, hweights, fun n hn => herror (fun _ => (n : ℝ)) ⟨n, hn, rfl⟩⟩

theorem exists_freeze_normalized_cell (L : A.LowestLayerModel h)
    (g : ℕ → Fin D → ℤ) (z : Fin D → ℝ) {N : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : (2 : ℝ) ^ (h + 1) * δ < 1)
    (hfreeze : (D : ℝ) * (2 * δ) < 1 / 12)
    (hcell : ∀ n < N, ∀ i,
      ‖aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - g n i - z i‖ ≤ δ) :
    ∃ F : PolynomialPatch Unit s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ n < N, dist (A.value (fun _ => (n : ℝ))) (F.value (fun _ => (n : ℝ))) ≤
        A.kernel.lip * ((D : ℝ) * (2 * δ)) := by
  by_cases hex : ∃ n < N, ∃ b : Fin (D + E) → ℤ,
      A.kernel.value ((A.form.slots (fun _ => (n : ℝ))).residual b) ≠ 0
  · obtain ⟨n, hn, b, hb⟩ := hex
    exact L.exists_freeze_normalized_cell_at g z hδ hsmall hfreeze hcell hn b hb
  · let base := A.freezePrefix (fun _ : Fin D => (0 : MvPolynomial Unit ℝ))
      (fun _ => (weightedSupportLE _ _).zero_mem) (0 : Fin D → ℝ)
    let F : PolynomialPatch Unit s E := { base with kernel := PatchKernel.zeroWithLip E A.kernel.lip }
    have hF (t : Unit → ℝ) : F.value t = 0 := by
      apply (F.form.slots t).patchValue_eq_zero F.kernel
      intro b
      rfl
    have hA (n : ℕ) (hn : n < N) : A.value (fun _ => (n : ℝ)) = 0 := by
      apply (A.form.slots (fun _ => (n : ℝ))).patchValue_eq_zero A.kernel
      intro b
      exact not_ne_iff.mp (fun hb => hex ⟨n, hn, b, hb⟩)
    refine ⟨F, rfl, (fun _ => rfl), ?_⟩
    intro n hn
    rw [hA n hn, hF, dist_self]
    positivity

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem PolynomialCoordinatePartitionBound.freeze_layer {h p : ℕ} {K : ℝ}
    (hpartition : PolynomialCoordinatePartitionBound.{0} h K p)
    {s D E N H : ℕ} (A : PolynomialPatch Unit s (D + E)) (L : A.LowestLayerModel h)
    (hH : 0 < H) (hscale : K * ((D : ℝ) + 1) ≤ H)
    (hsize : H ^ (p * (D + 1) ^ (2 * h)) ≤ N)
    (hsmall : (2 : ℝ) ^ (h + 1) * ((h : ℝ) / H) < 1)
    (hfreeze : (D : ℝ) * (2 * ((h : ℝ) / H)) < 1 / 12) :
    ∃ (Q : FiniteProgressionPartition N) (F : Q.Label → PolynomialPatch Unit s E),
      Fintype.card Q.Label * H ≤ 2 ^ h * N ∧
      ∀ i, (F i).kernel.lip = A.kernel.lip ∧
        (∀ j, (F i).weight j = A.weight (j.natAdd D)) ∧
        ∀ n < Q.length i,
          dist (A.value (fun _ => ((Q.start i + Q.step i * n : ℕ) : ℝ)))
            ((F i).value (fun _ => (n : ℝ))) ≤ A.kernel.lip * ((D : ℝ) * (2 * ((h : ℝ) / H))) := by
  let P := fun i => MvPolynomial.uniqueAlgEquiv ℝ Unit (L.normalizedOrigin i)
  have hP : ∀ i, (P i).natDegree ≤ h := fun i => singleParameter_natDegree_le (L.normalizedOrigin_degree i)
  obtain ⟨Q, z, m, hcount, herror⟩ := hpartition (Fin D) P hP N H hH
    (by simpa only [Fintype.card_fin] using hscale) (by simpa only [Fintype.card_fin] using hsize)
  have hcell (i : Q.Label) :
      ∃ F : PolynomialPatch Unit s E, F.kernel.lip = A.kernel.lip ∧
        (∀ j, F.weight j = A.weight (j.natAdd D)) ∧
        ∀ n < Q.length i,
          dist (A.value (fun _ => ((Q.start i + Q.step i * n : ℕ) : ℝ)))
            (F.value (fun _ => (n : ℝ))) ≤ A.kernel.lip * ((D : ℝ) * (2 * ((h : ℝ) / H))) := by
    let L' := L.onAffineLine (fun _ => (Q.start i : ℝ)) (fun _ => (Q.step i : ℝ))
    have hclose : ∀ n < Q.length i, ∀ j,
        ‖aeval (fun _ : Unit => (n : ℝ)) (L'.normalizedOrigin j) - m i n j - z i j‖ ≤ (h : ℝ) / H := by
      intro n hn j
      change ‖aeval (fun _ : Unit => (n : ℝ))
        ((L.onAffineLine _ _).normalizedOrigin j) - m i n j - z i j‖ ≤ _
      rw [PolynomialPatch.LowestLayerModel.onAffineLine_normalizedOrigin_eval]
      have he := herror i n hn j
      simpa only [P, singleParameter_eval, Nat.cast_add, Nat.cast_mul, Real.norm_eq_abs] using he
    obtain ⟨F, hFlip, hFweights, hFerr⟩ := L'.exists_freeze_normalized_cell (m i) (z i)
      (by positivity : 0 ≤ (h : ℝ) / H) hsmall hfreeze hclose
    refine ⟨F, hFlip, hFweights, ?_⟩
    intro n hn
    have he := hFerr n hn
    rw [PolynomialPatch.onAffineLine_value] at he
    change dist (A.value _) (F.value _) ≤ A.kernel.lip * _ at he
    simpa only [Nat.cast_add, Nat.cast_mul] using he
  choose F hFlip hFweights hFerr using hcell
  exact ⟨Q, F, hcount, fun i => ⟨hFlip i, hFweights i, hFerr i⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NormalizedLayerScoreStep
namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

open scoped BigOperators

theorem exists_large_score_cell {N H : ℕ} (P : FiniteProgressionPartition N)
    (hN : 0 < N) (hH : 0 < H) (f B : ℕ → ℝ) (V : P.Label → ℕ → ℝ)
    {b σ ε C : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ) (hC : 0 < C)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ n < N, B n ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : 4 * ε ≤ σ) (hcount : (Fintype.card P.Label : ℝ) * H ≤ C * N)
    (hclose : ∀ i n, n < P.length i → dist (B (P.start i + P.step i * n)) (V i n) ≤ ε)
    (hscore : σ ≤ 𝔼 n : Fin N, (f n.val - b) * B n.val) :
    ∃ i, σ * H / (8 * C) ≤ P.length i ∧
      σ / 2 < 𝔼 n : Fin (P.length i), (f (P.start i + P.step i * n.val) - b) * V i n.val := by
  let : NeZero N := ⟨hN.ne'⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcost : (Fintype.card P.Label : ℝ) * (σ * H / (8 * C)) / N ≤ σ / 8 := by
    apply (div_le_iff₀ hNR).mpr
    rw [show (Fintype.card P.Label : ℝ) * (σ * H / (8 * C)) =
      ((Fintype.card P.Label : ℝ) * H * σ) / (8 * C) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 8 * C)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcount hσ.le]
  have hg (n : Fin N) : (f n.val - b) * B n.val ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (show f n.val - b ≤ 1 by linarith [(hf n.val n.isLt).2, hb.1])
      (hB n.val n.isLt).1
    nlinarith [(hB n.val n.isLt).2]
  obtain ⟨i, hlarge, hcell⟩ := exists_large_cell_score P.cell
    (fun n => (f n.val - b) * B n.val) (L := σ * H / (8 * C)) (τ := 3 * σ / 4)
    (by positivity) (by positivity) hg hscore (by simp only [Fintype.card_fin]; linarith)
  rw [P.card_cell] at hlarge
  have hlen : 0 < P.length i := by
    have hpos : (0 : ℝ) < σ * H / (8 * C) := by positivity
    have hlenR : (0 : ℝ) < P.length i := hpos.trans_le hlarge
    exact_mod_cast hlenR
  let : NeZero (P.length i) := ⟨hlen.ne'⟩
  have hcell' : 3 * σ / 4 < 𝔼 n : Fin (P.length i),
      (f (P.start i + P.step i * n.val) - b) * B (P.start i + P.step i * n.val) := by
    rw [P.expect_cell i (fun n => (f n - b) * B n)] at hcell
    exact hcell
  have hpoint (n : Fin (P.length i)) := weighted_score_le_of_close
    (hf _ (P.point_lt i n.isLt)) hb (hclose i n.val n.isLt)
  have hmean : (𝔼 n : Fin (P.length i),
      (f (P.start i + P.step i * n.val) - b) * B (P.start i + P.step i * n.val)) ≤
      (𝔼 n : Fin (P.length i), (f (P.start i + P.step i * n.val) - b) * V i n.val) + ε := by
    calc
      _ ≤ 𝔼 n : Fin (P.length i), ((f (P.start i + P.step i * n.val) - b) * V i n.val + ε) :=
        Finset.expect_le_expect fun n _ => hpoint n
      _ = _ := by rw [Finset.expect_add_distrib]; simp
  exact ⟨i, hlarge, by linarith⟩

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

theorem PolynomialCoordinatePartitionBound.layer_score_step {h p : ℕ} {K : ℝ}
    (hpartition : PolynomialCoordinatePartitionBound.{0} h K p)
    {s D E N H : ℕ} (A : PolynomialPatch Unit s (D + E)) (L : A.LowestLayerModel h)
    (hH : 0 < H) (hscale : K * ((D : ℝ) + 1) ≤ H)
    (hsize : H ^ (p * (D + 1) ^ (2 * h)) ≤ N)
    (hsmall : (2 : ℝ) ^ (h + 1) * ((h : ℝ) / H) < 1)
    (hfreeze : (D : ℝ) * (2 * ((h : ℝ) / H)) < 1 / 12)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b σ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hroom : 8 * (A.kernel.lip : ℝ) * D * h ≤ σ * H)
    (hscore : σ ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) :
    ∃ (q a len : ℕ) (F : PolynomialPatch Unit s E), 0 < q ∧
      σ * H / (2 : ℝ) ^ (h + 3) ≤ len ∧ (∀ n < len, a + q * n < N) ∧
      F.kernel.lip = A.kernel.lip ∧ (∀ j, F.weight j = A.weight (j.natAdd D)) ∧
      σ / 2 < 𝔼 n : Fin len, (f (a + q * n.val) - b) * F.value (fun _ => (n.val : ℝ)) := by
  obtain ⟨Q, F, hcount, hproperties⟩ := hpartition.freeze_layer A L hH hscale hsize hsmall hfreeze
  have hN : 0 < N := (pow_pos hH _).trans_le hsize
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcountR : (Fintype.card Q.Label : ℝ) * H ≤ (2 : ℝ) ^ h * N := by exact_mod_cast hcount
  have hroom' : 4 * ((A.kernel.lip : ℝ) * ((D : ℝ) * (2 * ((h : ℝ) / H)))) ≤ σ := by
    rw [show 4 * ((A.kernel.lip : ℝ) * ((D : ℝ) * (2 * ((h : ℝ) / H)))) =
      (8 * (A.kernel.lip : ℝ) * D * h) / H by ring]
    exact (div_le_iff₀ hHR).mpr hroom
  obtain ⟨i, hlarge, hretained⟩ := Q.exists_large_score_cell hN hH f
    (fun n => A.value (fun _ => (n : ℝ))) (fun i n => (F i).value (fun _ => (n : ℝ)))
    hb hσ (by positivity : 0 < (2 : ℝ) ^ h) hf (fun n _ => A.value_mem_Icc _)
    hroom' hcountR (fun i => (hproperties i).2.2) hscore
  refine ⟨Q.step i, Q.start i, Q.length i, F i, Q.step_pos i, ?_,
    (fun n hn => Q.point_lt i hn), (hproperties i).1, (hproperties i).2.1, hretained⟩
  have heq : (2 : ℝ) ^ (h + 3) = 8 * (2 : ℝ) ^ h := by rw [pow_add]; ring
  simpa only [heq] using hlarge

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ConstructLayerResetScales
namespace OAI

section

namespace Erdos3

theorem layerReset_exponent_polynomial (s p r : ℕ) :
    (2 * (p * (r + 1) ^ (2 * s))) ^ s = (2 * p) ^ s * (r + 1) ^ (2 * s * s) := by
  rw [← mul_assoc, mul_pow, ← pow_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace LayerResetScales

theorem reset_from {s r : ℕ} {L : ℝ} (S : LayerResetScales s r L)
    (m h : ℕ) (hh : 0 < h) (hlevel : h + m = s + 1)
    {d N : ℕ} (A : PolynomialPatch Unit s d) (hrank : d ≤ r)
    (hlip : (A.kernel.lip : ℝ) ≤ L) (hweight : ∀ i, h ≤ A.weight i)
    (hN : S.threshold h ≤ N) (f : ℕ → ℝ)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hscore : S.score h ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) :
    ∃ q a len : ℕ, 0 < q ∧ S.threshold (s + 1) ≤ len ∧
      (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  induction m generalizing h d N f with
  | zero =>
    have heq : h = s + 1 := by omega
    have hd : d = 0 := by
      by_contra hn
      have hi : 0 < d := Nat.pos_of_ne_zero hn
      have hlo := hweight ⟨0, hi⟩
      have hhi := A.weight_le ⟨0, hi⟩
      omega
    subst d
    have hNpos : 0 < N := by
      by_contra hn
      have hz : N = 0 := by omega
      subst N
      have hs := S.score_pos h (by omega)
      have hz : S.score h ≤ 0 := by simpa using hscore
      exact (not_le_of_gt hs) hz
    let : NeZero N := ⟨hNpos.ne'⟩
    have hc : 0 ≤ A.kernel.value 0 := by
      simpa only [PolynomialPatch.value_rank_zero] using (A.value_mem_Icc (fun _ => 0)).1
    have hmean : 0 < (𝔼 n : Fin N, f n.val) - b := by
      have hs := (S.score_pos h (by omega)).trans_le hscore
      simp only [PolynomialPatch.value_rank_zero, ← Finset.expect_mul,
        Finset.expect_sub_distrib, Fintype.expect_const] at hs
      by_contra hn
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hc)) hs
    refine ⟨1, 0, N, by omega, ?_, ?_, ?_⟩
    · simpa only [heq] using hN
    · intro n hn
      simpa using hn
    · simpa using (show b < 𝔼 n : Fin N, f n.val by linarith)
  | succ m ih =>
    have hhs : h ≤ s := by omega
    obtain ⟨D, hD, hhead, htail⟩ := monotone_weight_layer A.weight A.weight_mono hweight
    obtain ⟨E, rfl⟩ := Nat.exists_eq_add_of_le hD
    have hDr : D ≤ r := by omega
    have hDrR : (D : ℝ) ≤ r := by exact_mod_cast hDr
    have hscale : S.constant h * ((D : ℝ) + 1) ≤ S.cellScale h :=
      (mul_le_mul_of_nonneg_left (by linarith : (D : ℝ) + 1 ≤ r + 1)
        (S.constant_nonneg h hhs)).trans (S.scale_bound h hhs)
    have hsize : S.cellScale h ^ (S.exponent h * (D + 1) ^ (2 * h)) ≤ N := by
      apply le_trans (Nat.pow_le_pow_right (S.cell_pos h hhs)
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hDr 1) _)))
      exact (S.power_bound h hhs).trans hN
    have hfreeze : (D : ℝ) * (2 * ((h : ℝ) / S.cellScale h)) < 1 / 12 :=
      (mul_le_mul_of_nonneg_right hDrR (by positivity)).trans_lt (S.freeze_error h hhs)
    have hroom : 8 * (A.kernel.lip : ℝ) * D * h ≤ S.score h * S.cellScale h := by
      apply le_trans _ (S.score_error h hhs)
      have hprod := mul_le_mul hlip hDrR (by positivity : (0 : ℝ) ≤ D)
        (A.kernel.lip.coe_nonneg.trans hlip)
      nlinarith [mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg (α := ℝ) h)]
    let model := A.lowestLayerModel hh (fun i => hhead (i.castAdd E) i.isLt)
    obtain ⟨q, a, len, F, hq, hlen, hin, hFlip, hFw, hretained⟩ :=
      (S.partition h hhs).layer_score_step A model (S.cell_pos h hhs) hscale hsize
        (S.lift_error h hhs) hfreeze f hf hb (S.score_pos h (by omega)) hroom hscore
    have hnext : S.threshold (h + 1) ≤ len := by
      exact_mod_cast (S.length_bound h hhs).trans hlen
    have hw : ∀ i, h + 1 ≤ F.weight i := by
      intro i
      rw [hFw]
      exact htail _ (by simp)
    obtain ⟨q', a', len', hq', hlen', hin', hdense⟩ := ih (h + 1) (by omega) (by omega)
      F (by omega) (by simpa only [hFlip] using hlip) hw hnext
      (fun n => f (a + q * n)) (fun n hn => hf _ (hin n hn))
      ((S.score_next h hhs).trans hretained.le)
    refine ⟨q * q', a + q * a', len', Nat.mul_pos hq hq', hlen', ?_, ?_⟩
    · intro n hn
      convert hin (a' + q' * n) (hin' n hn) using 1
      ring
    · convert hdense using 1
      congr 1
      funext n
      congr 1
      ring

theorem density_increment {s r : ℕ} {L : ℝ} (S : LayerResetScales s r L)
    {d N : ℕ} (A : PolynomialPatch Unit s d) (hrank : d ≤ r)
    (hlip : (A.kernel.lip : ℝ) ≤ L) (hN : S.threshold 1 ≤ N)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hscore : S.score 1 ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) :
    ∃ q a len : ℕ, 0 < q ∧ S.threshold (s + 1) ≤ len ∧
      (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) :=
  S.reset_from s 1 (by omega) (by omega) A hrank hlip A.weight_pos hN f hf hb hscore

end LayerResetScales
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchDensityIncrement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_patch_density_increment_s2_oai (s : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (d N T : ℕ) (A : PolynomialPatch Unit s d), 0 < T →
        K * ((d : ℝ) + 1) ≤ T →
        (2 : ℝ) ^ (s + 1) * s < T → 24 * (d : ℝ) * s < T →
        T ^ ((2 * p) ^ s * (d + 1) ^ (2 * s * s)) ≤ N →
        ∀ f : ℕ → ℝ, (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        8 * (A.kernel.lip : ℝ) * d * s * (2 : ℝ) ^ s ≤ σ * T →
        (2 : ℝ) ^ (2 * s + 3) ≤ σ * T →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ T ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_uniform_coordinate_partition_bound.{0} s
  refine ⟨K, p, hK, hp, ?_⟩
  intro d N T A hT hscale hlift hfreeze hsize f hf b σ hb hσ hroom hlength hscore
  let S := powerLayerResetScales hp (by linarith : 0 ≤ K) A.kernel.lip.coe_nonneg
    hT hσ hpartition hscale hlift hfreeze hroom hlength
  have hN : S.threshold 1 ≤ N := by
    change T ^ ((2 * (p * (d + 1) ^ (2 * s))) ^ s) ≤ N
    rw [layerReset_exponent_polynomial]
    exact hsize
  have hs : S.score 1 ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ)) := by
    change σ / (2 : ℝ) ^ 1 ≤ _
    exact (div_le_self hσ.le (by norm_num)).trans hscore
  obtain ⟨q, a, len, hq, hlen, hin, hdense⟩ := S.density_increment A le_rfl le_rfl hN f hf hb hs
  change layerResetThreshold s (p * (d + 1) ^ (2 * s)) T (s + 1) ≤ len at hlen
  rw [layerResetThreshold_terminal] at hlen
  exact ⟨q, a, len, hq, hlen, hin, hdense⟩

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.polynomial_patch_density_increment_s2_oai := @OAI.Erdos3.polynomial_patch_density_increment_s2_oai
