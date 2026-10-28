-- Prove2me | solution 1 for OAI.CoboundaryExpanders.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:30:48.830675+00:00
-- url     : https://prove2.me/submissions/a89c9c0f-fbde-4356-962b-836e9330ebc3

import Mathlib
import Definitions.Def_CoboundaryExpanders
import Definitions.Def_OAIQ3Cb002
import Theorems.Thm_OAI_CoboundaryExpanders_Construction_actual_uniform_cosystolic
import Theorems.Thm_OAI_CoboundaryExpanders_Construction_uniform_infinite_coset_positive
import Theorems.Thm_OAI_CoboundaryExpanders_uniform_gamma_vanishing

set_option allowUnsafeReducibility true in
attribute [local reducible] _root_.OAI.CoboundaryExpanders.Complex.Face
section
-- module Solutions.OAIQ3_Cob.Coboundary_Chains
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Augmented F2 simplicial chains, boundaries, exactness, and relative attachments.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains

section
variable {V : Type} [DecidableEq V]

namespace Complex
variable (X : CoboundaryExpanders.InfiniteChains.Complex V)

lemma embed_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    (X.embed (n+1)).comp (X.cone a ha n) = (rawCone a).comp (X.embed n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, cone,
    Finsupp.linearCombination_single, embed_single, rawCone_single]
  by_cases h : a ∈ s.val
  · rw [dite_eq_left h, smul_zero, map_zero, ite_eq_left h]
  · rw [dite_eq_right h, map_smul, embed_single, ite_eq_right h]
    simp

lemma contraction (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    (X.boundary (n+1)).comp (X.cone a ha (n+1)) +
      (X.cone a ha n).comp (X.boundary n) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply X.embed_injective (n+1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add]
  change (X.embed (n+1)).comp (X.boundary (n+1)) (X.cone a ha (n+1) c) +
    (X.embed (n+1)).comp (X.cone a ha n) (X.boundary n c) = _
  rw [embed_boundary, embed_cone]
  change rawBoundary ((X.embed (n+2)).comp (X.cone a ha (n+1)) c) +
    rawCone a ((X.embed n).comp (X.boundary n) c) = _
  rw [embed_boundary, embed_cone]
  exact LinearMap.congr_fun (raw_contraction a) (X.embed (n+1) c)

lemma boundary_exact_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    Function.Exact (X.boundary (n+1)) (X.boundary n) := by
  intro c
  constructor
  · intro hc
    refine ⟨X.cone a ha (n+1) c, ?_⟩
    have hh := LinearMap.congr_fun (X.contraction a ha n) c
    simpa [hc] using hh
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (X.boundary_squared n) b

open CategoryTheory

lemma chainComplex_exactAt_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    X.chainComplex.ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (X.chainComplex.d (n+2) (n+1)) (X.chainComplex.d (n+1) n)
  rw [chainComplex_d, chainComplex_d]
  exact (X.boundary_exact_of_cone a ha (n+1))

lemma chainComplex_homology_isZero_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    Limits.IsZero (X.chainComplex.homology (n+1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (X.chainComplex_exactAt_of_cone a ha n)

lemma full_isConePoint (a : V) : (full V).IsConePoint a := fun _ _ => Set.mem_univ _

end Complex
end

end CoboundaryExpanders.InfiniteChains

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite pure complexes, weighted F2 norms, distance to actual coboundaries, and the full main statement.
-/

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Complex

theorem weight_nonneg (X : Complex) (s i : ℕ) (σ : X.Face i) :
    0 ≤ X.weight s i σ := by
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

attribute [local instance] OAI.CoboundaryExpanders.Complex.instFintypeFace_1
theorem norm_nonneg (X : Complex) (s i : ℕ) (f : X.Cochain i) :
    0 ≤ X.norm s i f := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact X.weight_nonneg s i σ
  · exact le_rfl

theorem coboundaries_nonempty (X : Complex) (i : ℕ) :
    (X.coboundaries i).Nonempty := ⟨0, X.zero_mem_coboundaries i⟩

theorem distance_attained (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) (hA : A.Nonempty) :
    ∃ a ∈ A, X.distance s i f A = X.norm s i (f - a) := by
  have hfin : (((fun a => X.norm s i (f - a)) '' A) : Set ℝ).Finite :=
    (Set.toFinite A).image _
  obtain ⟨a, ha, heq⟩ := (hA.image (fun a => X.norm s i (f - a))).csInf_mem hfin
  exact ⟨a, ha, heq.symm⟩

theorem distance_le_norm (X : Complex) (s i : ℕ) (f : X.Cochain i)
    {A : Set (X.Cochain i)} {a : X.Cochain i} (ha : a ∈ A) :
    X.distance s i f A ≤ X.norm s i (f - a) := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨b, _, rfl⟩; exact X.norm_nonneg s i (f - b)⟩
  · exact ⟨a, ha, rfl⟩

theorem sum_face_eq {A : Type*} [AddCommMonoid A] (X : Complex) (i : ℕ)
    (g : Finset (Fin X.vertexCount) → A) :
    (∑ σ : X.Face i, g σ.val) = ∑ σ ∈ X.facesOf i, g σ :=
  (Finset.sum_subtype (X.facesOf i) (fun _ => Iff.rfl) g).symm

theorem cofaceCount_eq_sum (X : Complex) (s : ℕ) (σ : Finset (Fin X.vertexCount)) :
    X.cofaceCount s σ = ∑ τ : X.Face s, if σ ⊆ τ.val then (1 : ℕ) else 0 := by
  rw [sum_face_eq X s (fun τ => if σ ⊆ τ then (1 : ℕ) else 0), Finset.sum_boole]
  rfl

theorem sum_cofaceCount {X : Complex} {i s n : ℕ} (σ : X.Face i) (his : i ≤ s) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.cofaceCount n ρ.val else 0) =
    X.cofaceCount n σ.val * Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
  classical
  calc
    _ = ∑ ρ : X.Face s, ∑ τ : X.Face n,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro ρ _
      by_cases h : σ.val ⊆ ρ.val <;> simp [h, cofaceCount_eq_sum]
    _ = ∑ τ : X.Face n, ∑ ρ : X.Face s,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ τ : X.Face n, if σ.val ⊆ τ.val then
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) else 0 := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hστ : σ.val ⊆ τ.val
      · rw [ite_eq_left hστ, Finset.sum_boole]
        exact card_between_faces σ τ hστ his
      · rw [ite_eq_right hστ]
        apply Finset.sum_eq_zero
        intro ρ _
        exact ite_eq_right (fun h => hστ (h.1.trans h.2))
    _ = _ := by
      rw [cofaceCount_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> simp

theorem sum_cofaceCount_real {X : Complex} {i s n : ℕ} (σ : X.Face i) (his : i ≤ s) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then (X.cofaceCount n ρ.val : ℝ) else 0) =
    (X.cofaceCount n σ.val : ℝ) * Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
  exact_mod_cast sum_cofaceCount (n := n) σ his

theorem facesOf_nonempty_of_pure {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) : (X.facesOf s).Nonempty := by
  obtain ⟨τ, hτ⟩ := hX.1
  have hτcard := ((mem_facesOf X n τ).mp hτ).2
  obtain ⟨σ, hστ, hσcard⟩ := Finset.exists_subset_card_eq
    (show s + 1 ≤ τ.card by omega)
  exact ⟨σ, (mem_facesOf X s σ).mpr
    ⟨X.downward ((mem_facesOf X n τ).mp hτ).1 hστ, hσcard⟩⟩

theorem weight_eq_cofaceCount (X : Complex) (n i : ℕ) (σ : X.Face i) :
    X.weight n i σ = (X.cofaceCount n σ.val : ℝ) /
      ((Nat.choose (n + 1) (i + 1) : ℝ) * (X.facesOf n).card) := rfl

theorem weight_averaging {X : Complex} {i s n : ℕ} (hX : (X.facesOf n).Nonempty)
    (his : i ≤ s) (hsn : s ≤ n) (σ : X.Face i) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight n s ρ else 0) =
      (Nat.choose (s + 1) (i + 1) : ℝ) * X.weight n i σ := by
  classical
  have hF : ((X.facesOf n).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hX.card_pos)
  have hAi : (Nat.choose (n + 1) (i + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ (his.trans hsn))))
  have hAs : (Nat.choose (n + 1) (s + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
  have hchoose :
      (Nat.choose (n + 1) (s + 1) : ℝ) * Nat.choose (s + 1) (i + 1) =
      (Nat.choose (n + 1) (i + 1) : ℝ) *
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
    exact_mod_cast Nat.choose_mul (n := n + 1) (Nat.succ_le_succ his)
  calc
    _ = (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then (X.cofaceCount n ρ.val : ℝ) else 0) /
        ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ρ _
      split_ifs <;> simp [weight_eq_cofaceCount]
    _ = ((X.cofaceCount n σ.val : ℝ) *
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1))) /
        ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) := by
      rw [sum_cofaceCount_real σ his]
    _ = _ := by
      rw [weight_eq_cofaceCount]
      field_simp
      linear_combination -(X.cofaceCount n σ.val : ℝ) * hchoose

@[simp] theorem weight_top {X : Complex} {s : ℕ} (σ : X.Face s) :
    X.weight s s σ = 1 / (X.facesOf s).card := by
  simp [weight_eq_cofaceCount]

theorem skeletonScale_pos {X : Complex} {n s : ℕ} (hX : X.Pure n) (hsn : s ≤ n) :
    0 < X.skeletonScale n s := by
  exact div_pos
    (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
      (Nat.cast_pos.mpr hX.1.card_pos))
    (Nat.cast_pos.mpr (facesOf_nonempty_of_pure hX hsn).card_pos)

theorem skeletonScale_mul_topweight {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) (ρ : X.Face s) :
    X.skeletonScale n s * X.weight n s ρ =
      (X.cofaceCount n ρ.val : ℝ) * X.weight s s ρ := by
  have hCount : ((X.facesOf n).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hX.1.card_pos)
  have hChoose : (Nat.choose (n + 1) (s + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
  rw [skeletonScale, weight_eq_cofaceCount, weight_top]
  field_simp

theorem skeleton_topweight_comparison {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (ρ : X.Face s) :
    (X.skeletonScale n s / b) * X.weight n s ρ ≤ X.weight s s ρ ∧
      X.weight s s ρ ≤ (X.skeletonScale n s / a) * X.weight n s ρ := by
  have heq := skeletonScale_mul_topweight hX hsn ρ
  have hw := X.weight_nonneg s s ρ
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hb, heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcount ρ).2 hw
  · rw [div_mul_eq_mul_div, le_div_iff₀ ha, heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcount ρ).1 hw

theorem skeleton_weight_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (σ : X.Face i) :
    (X.skeletonScale n s / b) * X.weight n i σ ≤ X.weight s i σ ∧
      X.weight s i σ ≤ (X.skeletonScale n s / a) * X.weight n i σ := by
  classical
  have hXs := facesOf_nonempty_of_pure hX hsn
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hb : 0 < b := (ha.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  have hB : (0 : ℝ) < Nat.choose (s + 1) (i + 1) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ his))
  have sum_scaled (c : ℝ) (t : ℕ) :
      (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then c * X.weight t s ρ else 0) =
      c * ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight t s ρ else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  constructor
  · have hlo :
        (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then
          (X.skeletonScale n s / b) * X.weight n s ρ else 0) ≤
        ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight s s ρ else 0 := by
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact (skeleton_topweight_comparison hX hsn ha hb hcount ρ).1
      · exact le_rfl
    rw [sum_scaled, weight_averaging hX.1 his hsn σ,
      weight_averaging hXs his le_rfl σ] at hlo
    apply (mul_le_mul_iff_right₀ hB).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hlo
  · have hhi :
        (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight s s ρ else 0) ≤
        ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then
          (X.skeletonScale n s / a) * X.weight n s ρ else 0 := by
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact (skeleton_topweight_comparison hX hsn ha hb hcount ρ).2
      · exact le_rfl
    rw [sum_scaled, weight_averaging hX.1 his hsn σ,
      weight_averaging hXs his le_rfl σ] at hhi
    apply (mul_le_mul_iff_right₀ hB).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hhi

theorem norm_le_of_weight_le {X : Complex} {r s i : ℕ} {c : ℝ}
    (hw : ∀ σ : X.Face i, X.weight r i σ ≤ c * X.weight s i σ)
    (f : X.Cochain i) : X.norm r i f ≤ c * X.norm s i f := by
  rw [norm, norm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · exact hw σ
  · simp

theorem distance_le_of_weight_le {X : Complex} {r s i : ℕ} {c : ℝ}
    (hw : ∀ σ : X.Face i, X.weight r i σ ≤ c * X.weight s i σ)
    (f : X.Cochain i) {A : Set (X.Cochain i)} (hA : A.Nonempty) :
    X.distance r i f A ≤ c * X.distance s i f A := by
  obtain ⟨a, ha, heq⟩ := X.distance_attained s i f A hA
  rw [heq]
  exact (X.distance_le_norm r i f ha).trans (norm_le_of_weight_le hw (f - a))

theorem skeleton_norm_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (f : X.Cochain i) :
    (X.skeletonScale n s / b) * X.norm n i f ≤ X.norm s i f ∧
      X.norm s i f ≤ (X.skeletonScale n s / a) * X.norm n i f := by
  constructor
  · rw [norm, norm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    split_ifs
    · exact (skeleton_weight_comparison hX his hsn ha hcount σ).1
    · simp
  · exact norm_le_of_weight_le
      (fun σ => (skeleton_weight_comparison hX his hsn ha hcount σ).2) f

theorem skeleton_distance_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (f : X.Cochain i) {A : Set (X.Cochain i)} (hA : A.Nonempty) :
    (X.skeletonScale n s / b) * X.distance n i f A ≤ X.distance s i f A ∧
      X.distance s i f A ≤ (X.skeletonScale n s / a) * X.distance n i f A := by
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hb : 0 < b := (ha.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  constructor
  · obtain ⟨a₀, ha₀, heq⟩ := X.distance_attained s i f A hA
    rw [heq]
    exact (mul_le_mul_of_nonneg_left (X.distance_le_norm n i f ha₀)
      (le_of_lt (div_pos (skeletonScale_pos hX hsn) hb))).trans
      (skeleton_norm_comparison hX his hsn ha hcount (f - a₀)).1
  · exact distance_le_of_weight_le
      (fun σ => (skeleton_weight_comparison hX his hsn ha hcount σ).2) f hA

theorem skeleton_expansion_on_common_cochains {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i < s) (hsn : s ≤ n) {M η : ℝ}
    (hη : 0 ≤ η)
    (hcount : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧ X.cofaceCount n ρ.val ≤ M)
    (hvanish : X.cocycles i = X.coboundaries i)
    (hcosystolic : ∀ f : X.Cochain i,
      η * X.distance n i f (X.cocycles i) ≤ X.norm n (i + 1) (X.coboundary i f))
    (f : X.Cochain i) :
    (η / M) * X.distance s i f (X.coboundaries i) ≤
      X.norm s (i + 1) (X.coboundary i f) := by
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hM : 0 < M := (zero_lt_one.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  have hΛ : 0 < X.skeletonScale n s := skeletonScale_pos hX hsn
  have hdist := (skeleton_distance_comparison hX his.le hsn zero_lt_one hcount
    f (X.coboundaries_nonempty i)).2
  simp only [div_one] at hdist
  have hexp := hcosystolic f
  rw [hvanish] at hexp
  calc
    _ ≤ (η / M) * (X.skeletonScale n s * X.distance n i f (X.coboundaries i)) :=
      mul_le_mul_of_nonneg_left hdist (div_nonneg hη hM.le)
    _ = (X.skeletonScale n s / M) *
        (η * X.distance n i f (X.coboundaries i)) := by ring
    _ ≤ (X.skeletonScale n s / M) * X.norm n (i + 1) (X.coboundary i f) :=
      mul_le_mul_of_nonneg_left hexp (div_nonneg hΛ.le hM.le)
    _ ≤ _ := (skeleton_norm_comparison hX his hsn zero_lt_one hcount
      (X.coboundary i f)).1

theorem skeleton_pure {X : Complex} {n s : ℕ} (hX : X.Pure n) (hsn : s ≤ n) :
    (X.skeleton s).Pure s := by
  refine ⟨?_, ?_⟩
  · rw [skeleton_facesOf le_rfl]
    exact facesOf_nonempty_of_pure hX hsn
  · intro σ hσ
    obtain ⟨hσX, hσs⟩ := (mem_skeleton_faces X s σ).mp hσ
    obtain ⟨τ, hτ, hστ⟩ := hX.2 σ hσX
    obtain ⟨ρ, hσρ, hρτ, hρcard⟩ := Finset.exists_subsuperset_card_eq hστ hσs
      (by rw [((mem_facesOf X n τ).mp hτ).2]; exact Nat.succ_le_succ hsn)
    refine ⟨ρ, ?_, hσρ⟩
    rw [skeleton_facesOf le_rfl]
    exact (mem_facesOf X s ρ).mpr ⟨X.downward ((mem_facesOf X n τ).mp hτ).1 hρτ,
      hρcard⟩

theorem skeleton_connected {X : Complex} (hX : X.Connected) {s : ℕ} (hs : 1 ≤ s) :
    (X.skeleton s).Connected := by
  refine ⟨hX.1, fun v w => ?_⟩
  apply Relation.ReflTransGen.mono (fun a b hab => ?_) v w (hX.2 v w)
  refine ⟨hab.1, (mem_skeleton_faces X s _).mpr ⟨hab.2, ?_⟩⟩
  have hcard := Finset.card_insert_le a ({b} : Finset (Fin X.vertexCount))
  simp only [Finset.card_singleton] at hcard
  omega

theorem skeleton_coboundaries (X : Complex) {i s : ℕ} (his : i ≤ s) :
    (X.skeletonCochainEquiv his) '' X.coboundaries i =
      (X.skeleton s).coboundaries i := by
  ext f
  cases i with
  | zero =>
    constructor
    · rintro ⟨g, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨fun _ => c, ⟨c, rfl⟩, rfl⟩
  | succ i =>
    have hi : i < s := his
    constructor
    · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
      exact ⟨X.skeletonCochainEquiv hi.le a, X.skeleton_coboundary hi a⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a₀, rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective a
      exact ⟨X.coboundary i a₀, ⟨a₀, rfl⟩, (X.skeleton_coboundary hi a₀).symm⟩

theorem skeleton_expansion {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i < s) (hsn : s ≤ n) {M η : ℝ}
    (hη : 0 ≤ η)
    (hcount : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧ X.cofaceCount n ρ.val ≤ M)
    (hvanish : X.cocycles i = X.coboundaries i)
    (hcosystolic : ∀ f : X.Cochain i,
      η * X.distance n i f (X.cocycles i) ≤ X.norm n (i + 1) (X.coboundary i f))
    (f : (X.skeleton s).Cochain i) :
    (η / M) * (X.skeleton s).distance s i f ((X.skeleton s).coboundaries i) ≤
      (X.skeleton s).norm s (i + 1) ((X.skeleton s).coboundary i f) := by
  obtain ⟨f₀, rfl⟩ := (X.skeletonCochainEquiv his.le).surjective f
  rw [← X.skeleton_coboundaries his.le, skeleton_distance_image,
    skeleton_coboundary X his, skeleton_norm]
  exact skeleton_expansion_on_common_cochains hX his hsn hη hcount hvanish hcosystolic f₀

theorem card_facesOf_zero (X : Complex) : (X.facesOf 0).card = X.vertexCount := by
  have h := Fintype.card_congr X.vertexFaceEquiv
  simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm

theorem coboundary_zero_degree (X : Complex) (f : X.Cochain 0) (τ : X.Face 1) :
    X.coboundary 0 f τ = ∑ v ∈ τ.val, f (X.vertexFaceEquiv v) := by
  rw [coboundary, ← Equiv.sum_comp X.vertexFaceEquiv]
  simp only [vertexFaceEquiv_val, Finset.singleton_subset_iff, Finset.sum_ite_mem,
    Finset.univ_inter]

@[simp] theorem coboundary_const (X : Complex) (c : ZMod 2) :
    X.coboundary 0 (fun _ => c) = 0 := by
  ext τ
  rw [coboundary_zero_degree]
  simp only [Finset.sum_const, face_card, Nat.reduceAdd, Pi.zero_apply, nsmul_eq_mul]
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [Nat.cast_ofNat, htwo, zero_mul]

theorem coboundaries_subset_cocycles (X : Complex) (i : ℕ) :
    X.coboundaries i ⊆ X.cocycles i := by
  cases i with
  | zero =>
    rintro f ⟨c, rfl⟩
    exact X.coboundary_const c
  | succ i =>
    rintro f ⟨g, rfl⟩
    exact X.coboundary_coboundary i g

theorem cocycles_zero_eq_coboundaries_of_connected {X : Complex} (hX : X.Connected) :
    X.cocycles 0 = X.coboundaries 0 := by
  apply Set.Subset.antisymm
  · intro f hf
    have hδ : X.coboundary 0 f = 0 := hf
    have hedge : ∀ v w : Fin X.vertexCount,
        v ≠ w ∧ {v, w} ∈ X.faces →
          f (X.vertexFaceEquiv v) = f (X.vertexFaceEquiv w) := by
      intro v w hvw
      let τ : X.Face 1 := ⟨{v, w}, (mem_facesOf X 1 _).mpr
        ⟨hvw.2, by simp [hvw.1]⟩⟩
      have he := congrFun hδ τ
      rw [coboundary_zero_degree] at he
      have hsum : f (X.vertexFaceEquiv v) + f (X.vertexFaceEquiv w) = 0 := by
        simpa [τ, hvw.1] using he
      have hchar : - f (X.vertexFaceEquiv w) = f (X.vertexFaceEquiv w) := by
        exact CharTwo.neg_eq _
      exact (eq_neg_of_add_eq_zero_left hsum).trans hchar
    have hpath : ∀ v w : Fin X.vertexCount,
        f (X.vertexFaceEquiv v) = f (X.vertexFaceEquiv w) := by
      intro v w
      induction hX.2 v w using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hab _ ih => exact (hedge _ _ hab).trans ih
    obtain ⟨v₀⟩ := hX.1
    refine ⟨f (X.vertexFaceEquiv v₀), ?_⟩
    funext σ
    obtain ⟨v, rfl⟩ := X.vertexFaceEquiv.surjective σ
    exact hpath v v₀
  · exact X.coboundaries_subset_cocycles 0

end CoboundaryExpanders.Complex

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Basic
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Polynomial congruence groups, truncation ideals, and finite nilpotent quotients.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix

namespace CoboundaryExpanders.Construction

section

theorem matrix_nilpotent_of_entries {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : A) (hx : IsNilpotent x)
    (M : Matrix ι ι A) (hM : ∀ i j, x ∣ M i j) : IsNilpotent M := by
  classical
  choose B hB using hM
  let B' : Matrix ι ι A := B
  have he : M = x • B' := by ext i j; exact hB i j
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [he, smul_pow, hr, zero_smul]

theorem prime_cast_trunc (p m : ℕ) : (p : Trunc p m) = 0 := by
  have h : (p : R p) = 0 := by simp
  rw [← map_natCast (Ideal.Quotient.mk (powerIdeal p m)), h, map_zero]

theorem reduction_sub_one_nilpotent (q a m : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin a) (R q)) (hA : A ∈ Gamma q a 1) :
    IsNilpotent
      ((Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal q m)) A :
        Matrix (Fin a) (Fin a) (Trunc q m)) - 1) := by
  apply matrix_nilpotent_of_entries (tbar q m) ⟨m, tbar_pow q m⟩
  intro i j
  have hd := (mem_gamma_iff q a 1 A).mp hA i j
  rw [pow_one] at hd
  obtain ⟨b, hb⟩ := hd
  refine ⟨Ideal.Quotient.mk (powerIdeal q m) b, ?_⟩
  have he := congrArg (Ideal.Quotient.mk (powerIdeal q m)) hb
  simp only [map_sub, map_mul] at he
  simpa [Matrix.sub_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply, tbar] using he

theorem reduction_prime_power (p a m : ℕ) (hp : p.Prime)
    (A : Matrix.SpecialLinearGroup (Fin a) (R p)) (hA : A ∈ Gamma p a 1) :
    ∃ r : ℕ, (Matrix.SpecialLinearGroup.map
      (Ideal.Quotient.mk (powerIdeal p m)) A) ^ p ^ r = 1 := by
  let B := Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A
  have hc : (p : Matrix (Fin a) (Fin a) (Trunc p m)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply, prime_cast_trunc]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent hp hc
    ((B : Matrix (Fin a) (Fin a) (Trunc p m)) - 1)
    (reduction_sub_one_nilpotent p a m A hA)
  refine ⟨r, ?_⟩
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    add_sub_cancel] using hr

theorem deeperCongruence_eq (p a m n : ℕ) :
    deeperCongruence p a m n = (Gamma p a n).subgroupOf (Gamma p a m) := rfl

theorem isPGroup_congruenceRange (p a m n : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    IsPGroup p (congruenceReduction p a m n).range := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  obtain ⟨A, hA⟩ := g.property
  obtain ⟨r, hr⟩ := reduction_prime_power p a n hp A
    (gamma_antitone p a hm A.property)
  refine ⟨r, Subtype.ext ?_⟩
  change (g : Matrix.SpecialLinearGroup (Fin a) (Trunc p n)) ^ p ^ r = 1
  rw [← hA]
  exact hr

theorem isPGroup_congruenceQuotient (p a m n : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    IsPGroup p (Gamma p a m ⧸ deeperCongruence p a m n) :=
  (isPGroup_congruenceRange p a m n hp hm).of_surjective
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n)).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n)).symm.surjective

theorem odd_congruence_index (p a m n : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hm : 1 ≤ m) : Odd (Nat.card (Gamma p a m ⧸ deeperCongruence p a m n)) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (isPGroup_congruenceQuotient p a m n hp hm).exists_card_eq
  rw [hr]
  exact hodd.pow

theorem upperUnitriangular_isPGroup (p a : ℕ) (hp : p.Prime) [NeZero p] :
    IsPGroup p (upperUnitriangular p a) := by
  intro g
  have hn : IsNilpotent ((g.val : Matrix (Fin a) (Fin a) (ZMod p)) - 1) := by
    refine ⟨a, strict_upper_pow_zero a _ ?_⟩
    intro i j hij
    rw [Matrix.sub_apply, g.property i j hij, sub_self]
  have hc : (p : Matrix (Fin a) (Fin a) (ZMod p)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent hp hc _ hn
  refine ⟨r, Subtype.ext (Subtype.ext ?_)⟩
  simpa only [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow,
    Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, add_sub_cancel] using hr

theorem gquot_isPGroup (p a m : ℕ) (hp : p.Prime) [NeZero p] : IsPGroup p (Gquot p a m) := by
  have himage : IsPGroup p (uReduction p a m).range := by
    intro g
    obtain ⟨A, hA⟩ := g.property
    have hpU := upperUnitriangular_isPGroup p a hp
      ⟨evalZero p a A.val, A.property⟩
    obtain ⟨r, hr⟩ := hpU
    have hgamma : A.val ^ p ^ r ∈ Gamma p a 1 := by
      rw [gamma_one_eq_ker_evalZero, MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hr
    obtain ⟨s, hs⟩ := reduction_prime_power p a m hp _ hgamma
    refine ⟨r + s, Subtype.ext ?_⟩
    change g.val ^ p ^ (r + s) = 1
    rw [← hA, pow_add, pow_mul]
    simpa only [map_pow, uReduction, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype] using hs
  exact himage.of_surjective
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).symm.surjective

theorem odd_gquot_card (p a m : ℕ) (hp : p.Prime) (hodd : Odd p) [NeZero p] :
    Odd (Nat.card (Gquot p a m)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (gquot_isPGroup p a m hp).exists_card_eq
  rw [hr]
  exact hodd.pow

end

variable (p n : ℕ) [Fact p.Prime]

theorem localGroup_card_le (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Nat.card (localGroup p n hn cut) ≤
      Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p)) := by
  exact (Nat.card_le_card_of_injective (localGroupEmbedding p n hn cut)
    (localGroupEmbedding p n hn cut).injective).trans
    (Nat.card_le_card_of_surjective _
      (Matrix.GeneralLinearGroup.map (n := Fin (n + 1))
        (algebraMap (ZMod p) (Frac p))).rangeRestrict_surjective)

theorem reducedLocalMap_surjective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Function.Surjective (reducedLocalMap p n hn m cut) := by
  rintro ⟨g, h⟩
  obtain ⟨u, hu, e⟩ := h
  exact ⟨⟨u, hu⟩, Subtype.ext e⟩

theorem reducedLocalGroup_card_le (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Nat.card (reducedLocalGroup p n hn m cut) ≤
      Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p)) := by
  exact (Nat.card_le_card_of_surjective _ (reducedLocalMap_surjective p n hn m cut)).trans
    ((Nat.card_le_card_of_injective _ (uLocalEmbedding p n hn cut).injective).trans
      (localGroup_card_le p n hn cut))

theorem card_trunc (m : ℕ) : Nat.card (Trunc p m) = p ^ m := by
  let : Module.Finite (ZMod p) (Trunc p m) :=
    (Polynomial.monic_X.pow m).finite_quotient
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  congr 1
  change Module.finrank (ZMod p) (R p ⧸ Ideal.span {(Polynomial.X : R p) ^ m}) = m
  rw [finrank_quotient_span_eq_natDegree]
  simp

theorem reducedRoot_injective {a : ℕ} {i j : Fin a} (hij : i < j) (m : ℕ) :
    Function.Injective (reducedRoot p hij m) := by
  intro f g he
  have h := congrArg (fun x : (uReduction p a m).range => x.val i j) he
  simpa [reducedRoot, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply_ne hij.ne] using h

theorem gquot_card_lower (hn : 1 ≤ n) (m : ℕ) :
    p ^ m ≤ Nat.card (Gquot p (n + 1) m) := by
  let i : Fin (n + 1) := 0
  let j : Fin (n + 1) := ⟨1, by omega⟩
  have hij : i < j := by change (0 : ℕ) < 1; omega
  rw [← card_trunc p m]
  exact Nat.card_le_card_of_injective
    ((QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m)).symm ∘
      reducedRoot p hij m)
    ((QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m)).symm.injective.comp
      (reducedRoot_injective p hij m))

theorem localQuotientMap_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut : Fin (n + 1)) : Function.Injective (localQuotientMap p n hn m cut) := by
  intro A B h
  apply Subtype.ext
  apply localGroups_reduction_injective p n hn hm cut cut A B
  exact congrArg (fun g : Gquot p (n + 1) m =>
    (QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m) g).val) h

theorem localGroup_isPGroup (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    IsPGroup p (localGroup p n hn cut) :=
  (gquot_isPGroup p (n + 1) 2 Fact.out).of_injective
    (localQuotientMap p n hn 2 cut) (localQuotientMap_injective p n hn le_rfl cut)

theorem localGroup_odd (hn : 1 ≤ n) (hp : Odd p) (cut : Fin (n + 1)) :
    Odd (Nat.card (localGroup p n hn cut)) := by
  obtain ⟨r, hr⟩ := (localGroup_isPGroup p n hn cut).exists_card_eq
  rw [hr]
  exact hp.pow

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Elementary matrices, Euclidean generation, block matrices, and residue-field pivot arguments.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary
variable {A : Type*} [CommRing A] {n : ℕ}

theorem E_upper_one_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i.val + 1 = j.val), E (show i ≠ j by intro he; subst j; omega) (1 : A) ∈ H)
    {i j : Fin n} (hij : i < j) : E hij.ne (1 : A) ∈ H := by
  generalize hdiff : j.val - i.val = r
  induction r using Nat.strong_induction_on generalizing i j with
  | h r ih =>
    by_cases hadj : i.val + 1 = j.val
    · exact hE i j hadj
    · let k : Fin n := ⟨j.val - 1, by omega⟩
      have hik : i < k := by dsimp [k]; change i.val < j.val - 1; omega
      have hkj : k.val + 1 = j.val := by dsimp [k]; omega
      have hkj' : k < j := by change k.val < j.val; omega
      have hk := ih (k.val - i.val) (by omega) hik rfl
      simpa only [mul_one] using E_path_mem H hik.ne hkj'.ne hij.ne hk (hE k j hkj)

end CoboundaryExpanders.Elementary

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Elementary
variable {A F : Type*} [CommRing A] [CommRing F] {n : ℕ}

theorem off_clear_step (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : g ∈ B)
    (k : ℕ) (hk : k < n * n) (hc : OffCleared g k) :
    ∃ e ∈ H, e * g ∈ B ∧ OffCleared (e * g) (k + 1) := by
  have hn : 0 < n := by nlinarith
  let j : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
  let i : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
  have hkij : j.val * n + i.val = k := by
    dsimp [i, j]
    simpa [Nat.mul_comm] using Nat.div_add_mod k n
  by_cases hij : i = j
  · refine ⟨1, H.one_mem, by simpa using hg, ?_⟩
    rw [one_mul]
    intro a b hab hkey
    apply hc a b hab
    have hne : b.val * n + a.val ≠ k := by
      intro he
      have hai : a = i := by
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt a.isLt] using this
      have hbj : b = j := by
        apply Fin.ext
        have := congrArg (fun r => r / n) he
        simpa only [Nat.mul_comm b.val n, Nat.mul_add_div hn,
          Nat.div_eq_of_lt a.isLt, add_zero] using this
      exact hab (hai.trans (hij.trans hbj.symm))
    omega
  · obtain ⟨u, hu⟩ := hunit (g j j) (by simpa using hB g hg j j le_rfl)
    let c : A := -g i j * (↑(u⁻¹) : A)
    have he : E hij c ∈ H := by
      apply hE
      intro hji
      simp [c, hB g hg i j hji.le, hij]
    refine ⟨E hij c, he, B.mul_mem (hHB he) hg, ?_⟩
    intro a b hab hkey
    rw [E_mul_apply]
    by_cases ha : a = i
    · subst a
      rw [ite_eq_left rfl]
      by_cases hb : b = j
      · subst b
        rw [← hu]
        dsimp [c]
        rw [mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]
      · have hbj : b.val < j.val := by
          have hbval : b.val ≠ j.val := Fin.val_ne_of_ne hb
          have hb_le : b.val ≤ j.val := by
            by_contra hnot
            have hlt : j.val + 1 ≤ b.val := by omega
            have hmul := Nat.mul_le_mul_right n hlt
            nlinarith
          omega
        rw [hc j b (ne_of_gt (show b < j from hbj)) (by
          have hmul := Nat.mul_le_mul_right n (by omega : b.val + 1 ≤ j.val)
          have hjlt := j.isLt
          nlinarith), mul_zero, add_zero]
        apply hc i b hab
        have hmul := Nat.mul_le_mul_right n (by omega : b.val + 1 ≤ j.val)
        nlinarith
    · rw [ite_eq_right ha, add_zero]
      apply hc a b hab
      have hne : b.val * n + a.val ≠ k := by
        intro he
        apply ha
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt a.isLt] using this
      omega

theorem diagonalize_iwahori (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : g ∈ B) :
    ∃ h ∈ H, h * g ∈ B ∧ ∀ i j, i ≠ j → (h * g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n * n → ∃ h ∈ H, h * g ∈ B ∧ OffCleared (h * g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1, H.one_mem, by simpa using hg, by intro i j h h'; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hb, hc⟩ := ih (by omega)
      obtain ⟨e, he, hb', hc'⟩ := off_clear_step π B H hHB hB hunit hE
        (h * g) hb k (by omega) hc
      exact ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using hb',
        by simpa only [mul_assoc] using hc'⟩
  obtain ⟨h, hh, hb, hc⟩ := hsteps _ le_rfl
  refine ⟨h, hh, hb, fun i j hij => hc i j hij ?_⟩
  have hi := i.isLt
  have hj := j.isLt
  nlinarith

theorem D_mem (π : A →+* F) (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    {i j : Fin n} (hij : i < j) (u : Aˣ) (hu : π (↑u : A) = 1) : D hij.ne u ∈ H := by
  unfold D
  apply H.mul_mem
  · apply H.mul_mem
    · apply H.mul_mem
      · exact hE _ _ _ _ (by intro h; exact False.elim ((lt_asymm hij h)))
      · exact hE _ _ _ _ (by intro _; simp [hu])
    · exact hE _ _ _ _ (by intro h; exact False.elim ((lt_asymm hij h)))
  · exact hE _ _ _ _ (by intro _; simp [hu])

theorem diagonal_iwahori_mem (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) A) (hg : g ∈ B)
    (hdiag : ∀ i j, i ≠ j → g i j = 0) : g ∈ H := by
  have hsteps : ∀ k, k ≤ n → ∃ h ∈ H, h * g ∈ B ∧
      (∀ i j, i ≠ j → (h * g) i j = 0) ∧
      (∀ i : Fin (n + 1), i.val < k → (h * g) i i = 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hg, by simpa using hdiag,
        by intro i hi; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hb, hd, hc⟩ := ih (by omega)
      let i : Fin (n + 1) := ⟨k, by omega⟩
      have hilast : i < Fin.last n := by change k < n; omega
      obtain ⟨u, hu⟩ := hunit ((h * g) i i) (by simpa using hB (h * g) hb i i le_rfl)
      have hπu : π (u : A) = 1 := by rw [hu]; simpa using hB (h * g) hb i i le_rfl
      have hπinv : π (↑(u⁻¹) : A) = 1 := by
        have := congrArg π (Units.mul_inv u)
        simpa only [map_mul, map_one, hπu, one_mul] using this
      let e := D hilast.ne u⁻¹
      have he : e ∈ H := D_mem π H hE hilast u⁻¹ hπinv
      refine ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using B.mul_mem (hHB he) hb,
        ?_, ?_⟩
      · intro a b hab
        rw [mul_assoc, D_mul_apply, hd a b hab, mul_zero]
      · intro a ha
        rw [mul_assoc, D_mul_apply]
        by_cases hai : a = i
        · subst a
          rw [ite_eq_left rfl, ← hu]
          exact Units.inv_mul u
        · have halast : a ≠ Fin.last n := by intro heq; subst a; simp only [Fin.val_last] at ha; omega
          rw [ite_eq_right hai, ite_eq_right halast, one_mul]
          apply hc
          have hne : a.val ≠ k := fun h => hai (Fin.ext h)
          omega
  obtain ⟨h, hh, hb, hd, hc⟩ := hsteps n le_rfl
  have hmatrix : (h * g).val = Matrix.diagonal (fun i => (h * g) i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · rw [hd i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (h * g) i i = (1 : A) := by
    rw [← Matrix.det_diagonal, ← hmatrix]
    exact (h * g).property
  have hfirst : ∀ i : Fin n, (h * g) i.castSucc i.castSucc = 1 := fun i => hc _ i.isLt
  have hlast : (h * g) (Fin.last n) (Fin.last n) = 1 := by
    simpa only [Fin.prod_univ_castSucc, hfirst, Finset.prod_const_one, one_mul] using hdet
  have heq : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (h * g) i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      by_cases hilast : i = Fin.last n
      · subst i; exact hlast
      · apply hc
        have := i.isLt
        have := Fin.val_ne_of_ne hilast
        simp only [Fin.val_last] at this
        omega
    · rw [hd i j hij, Matrix.one_apply_ne hij]
  rw [eq_inv_of_mul_eq_one_right heq]
  exact H.inv_mem hh

theorem iwahori_mem_of_roots (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H) : B ≤ H := by
  intro g hg
  obtain ⟨h, hh, hb, hd⟩ := diagonalize_iwahori π B H hHB hB hunit hE g hg
  have hm := diagonal_iwahori_mem π B H hHB hB hunit hE (h * g) hb hd
  simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hh) hm

end CoboundaryExpanders.Elementary

end

section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary

section
variable {F : Type*} [Field F] {n : ℕ}

theorem lower_column_nonzero (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F))
    (j : Fin n) (hg : ColumnPrefix g j.val) :
    ∃ a : Fin n, j ≤ a ∧ g a j ≠ 0 := by
  classical
  by_contra! h
  have hs := inverse_column_sum g j j
  rw [ite_eq_left rfl] at hs
  have hz : (∑ a, g⁻¹ j a * g a j) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hja : j ≤ a
    · rw [h a hja, mul_zero]
    · rw [inverse_prefix_zero g hg (show a.val < j.val from lt_of_not_ge hja)
        (ne_of_gt (lt_of_not_ge hja)), zero_mul]
  exact zero_ne_one (hz.symm.trans hs)

theorem exists_unit_pivot
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (j : Fin n)
    (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧ IsUnit ((e * g) j j) := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧
    (e * g) j j ≠ 0 ∧ ((e * g) j j).natDegree = r
  have hex : ∃ r, P r := by
    obtain ⟨a, hja, ha⟩ := lower_column_nonzero g j hg
    by_cases haj : a = j
    · subst a
      exact ⟨(g j j).natDegree, 1, H.one_mem, by simpa using hg, by simpa using ha,
        by simp⟩
    · refine ⟨(g a j).natDegree, W (Ne.symm haj), W_mem H hE (Ne.symm haj),
        columnPrefix_W_mul hg (Ne.symm haj) le_rfl hja, ?_, ?_⟩
      · simpa [W_mul_apply] using ha
      · simp [W_mul_apply]
  obtain ⟨e, he, hpref, hp, hdegree⟩ := Nat.find_spec hex
  have hdiv : ∀ a : Fin n, j ≤ a → (e * g) j j ∣ (e * g) a j := by
    intro a hja
    by_cases haj : a = j
    · subst a; exact dvd_refl _
    · apply (EuclideanDomain.mod_eq_zero).mp
      by_contra hmod
      let c : (Polynomial F) := -((e * g) a j / (e * g) j j)
      let e' := W (Ne.symm haj) * E haj c * e
      have he' : e' ∈ H := H.mul_mem (H.mul_mem (W_mem H hE (Ne.symm haj)) (hE _ _ _ _)) he
      have hpre' : ColumnPrefix (e' * g) j.val := by
        dsimp only [e']
        rw [mul_assoc, mul_assoc]
        exact columnPrefix_W_mul (columnPrefix_E_mul hpref haj le_rfl c)
          (Ne.symm haj) le_rfl hja
      have hpiv : (e' * g) j j = (e * g) a j % (e * g) j j := by
        dsimp only [e']
        rw [mul_assoc, mul_assoc, W_mul_apply, ite_eq_left rfl, E_mul_apply, ite_eq_left rfl]
        rw [EuclideanDomain.mod_eq_sub_mul_div]
        dsimp [c]
        ring
      have hnew : P (((e * g) a j % (e * g) j j).natDegree) :=
        ⟨e', he', hpre', by rw [hpiv]; exact hmod, by rw [hpiv]⟩
      have hlt : (((e * g) a j % (e * g) j j).natDegree) < Nat.find hex := by
        rw [← hdegree]
        exact Polynomial.natDegree_lt_natDegree hmod (Polynomial.degree_mod_lt _ hp)
      exact Nat.find_min hex hlt hnew
  refine ⟨e, he, hpref, isUnit_of_dvd_one ?_⟩
  have hs := inverse_column_sum (e * g) j j
  rw [ite_eq_left rfl] at hs
  apply (show (e * g) j j ∣ ∑ a, (e * g)⁻¹ j a * (e * g) a j from ?_).trans
    (dvd_of_eq hs)
  apply Finset.dvd_sum
  intro a ha
  by_cases hja : j ≤ a
  · exact dvd_mul_of_dvd_right (hdiv a hja) _
  · rw [inverse_prefix_zero (e * g) hpref (show a.val < j.val from lt_of_not_ge hja)
      (ne_of_gt (lt_of_not_ge hja)), zero_mul]
    exact dvd_zero _

end

section
variable {F : Type*} [Field F] {n : ℕ}

theorem diagonalize_polynomial
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e * g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e * g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1, H.one_mem, by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e, he, hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k, by omega⟩
      obtain ⟨h, hh, hpref', hpiv⟩ := exists_unit_pivot H hE (e * g) j hpref
      obtain ⟨r, hr, hcol⟩ := clear_column H hE (h * (e * g)) j hpref' hpiv
      exact ⟨r * h * e, H.mul_mem (H.mul_mem hr hh) he, by simpa [mul_assoc, j] using hcol⟩
  obtain ⟨e, he, hpref⟩ := hsteps n le_rfl
  exact ⟨e, he, fun i j hij => hpref i j j.isLt hij⟩

end

section
variable {F : Type*} [Field F]

theorem polynomial_SL_mem_of_roots (n : ℕ)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) : g ∈ H := by
  cases n with
  | zero =>
    have hg : g = 1 := by ext i; exact Fin.elim0 i
    rw [hg]; exact H.one_mem
  | succ n =>
    obtain ⟨e, he, hd⟩ := diagonalize_polynomial H hE g
    have hm := diagonal_mem_of_roots H hE (e * g) hd
    simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem he) hm

end

variable {A : Type*} [CommRing A] {n : ℕ}

theorem mul_E_apply {i j : Fin n} (h : i ≠ j) (c : A)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (g * E h c : Matrix.SpecialLinearGroup (Fin n) A) a b =
      g a b + if b = j then g a i * c else 0 := by
  change (g.val * Matrix.transvection i j c) a b = _
  by_cases hb : b = j
  · subst b; simp [mul_comm]
  · simp [hb]

theorem elementary_commutes_of_complement {i j : Fin n} (hij : i ≠ j) (c : A)
    (g : Matrix.SpecialLinearGroup (Fin n) A)
    (hrow : ∀ b, g j b = (1 : Matrix (Fin n) (Fin n) A) j b)
    (hcol : ∀ a, g a i = (1 : Matrix (Fin n) (Fin n) A) a i) :
    Commute (E hij c) g := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  rw [E_mul_apply, mul_E_apply, hrow, hcol]
  by_cases ha : a = i
  · subst a; by_cases hb : b = j
    · subst b; simp
    · simp [hb, Ne.symm hb]
  · by_cases hb : b = j
    · subst b; simp [ha]
    · simp [ha, hb]

end CoboundaryExpanders.Elementary

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Elementary
open Polynomial
variable {F : Type*} [Field F] {n : ℕ}

theorem restricted_euclidean_descent (a b : Polynomial F)
    (ha : a.constantCoeff = 1) (hb : b.constantCoeff = 0)
    (hmod : b % a ≠ 0) :
    ∃ c d : Polynomial F, c.constantCoeff = 0 ∧
      (a + d * (b + c*a)).natDegree < a.natDegree := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let q := b / a
  let r := b % a
  have hr : r ≠ 0 := hmod
  have hdeg : r.natDegree < a.natDegree :=
    Polynomial.natDegree_lt_natDegree hmod (Polynomial.degree_mod_lt b ha0)
  have heq : b + (-q)*a = r := by
    dsimp [q,r]
    rw [EuclideanDomain.mod_eq_sub_mul_div]
    ring
  by_cases hq : q.constantCoeff = 0
  · refine ⟨-q, -(a/r), by simpa using hq, ?_⟩
    rw [heq]
    have heq' : a + (-(a/r))*r = a % r := by
      rw [EuclideanDomain.mod_eq_sub_mul_div]
      ring
    rw [heq']
    have hr0 : r.constantCoeff = 0 := by
      rw [← heq]
      simp only [map_add,map_mul,map_neg,hb,hq,zero_mul,neg_zero,add_zero]
    have hrem : a % r ≠ 0 := by
      intro h
      have hc := congrArg Polynomial.constantCoeff h
      rw [EuclideanDomain.mod_eq_sub_mul_div] at hc
      simp only [map_sub,map_mul,ha,hr0,zero_mul,sub_zero,map_zero] at hc
      exact one_ne_zero hc
    exact (Polynomial.natDegree_lt_natDegree hrem (Polynomial.degree_mod_lt a hr)).trans hdeg
  · let c := -q + C q.constantCoeff
    let d := C (-q.constantCoeff⁻¹)
    refine ⟨c,d,by simp [c],?_⟩
    have heq' : a + d*(b+c*a) = d*r := by
      have hc : b+c*a = r + C q.constantCoeff * a := by
        dsimp [c]
        rw [← heq]
        ring
      rw [hc]
      have hd : d * C q.constantCoeff = -1 := by
        dsimp only [d]
        rw [← map_mul, neg_mul, inv_mul_cancel₀ hq]
        simp
      calc
        a + d*(r+C q.constantCoeff*a) = a + (d*C q.constantCoeff)*a + d*r := by ring
        _ = d*r := by rw [hd]; ring
    rw [heq']
    apply lt_of_le_of_lt (Polynomial.natDegree_mul_le) _
    simpa [d] using hdeg

theorem exists_unit_pivot_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hgB : g ∈ B)
    (j : Fin n) (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ IsUnit ((e*g) j j) := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ ((e*g) j j).natDegree = r
  have hex : ∃ r, P r := ⟨(g j j).natDegree,1,H.one_mem,by simpa using hg,by simp⟩
  obtain ⟨e,he,hpref,hdegree⟩ := Nat.find_spec hex
  have hegB : e*g ∈ B := B.mul_mem (hHB he) hgB
  have hconst : ((e*g) j j).constantCoeff = 1 := by simpa using hB (e*g) hegB j j le_rfl
  have hdiv : ∀ a : Fin n, j ≤ a → (e*g) j j ∣ (e*g) a j := by
    intro a hja
    by_cases haj : a=j
    · subst a; exact dvd_refl _
    · apply (EuclideanDomain.mod_eq_zero).mp
      by_contra hmod
      have hja' : j < a := lt_of_le_of_ne hja (Ne.symm haj)
      have hb : ((e*g) a j).constantCoeff = 0 := by simpa [haj] using hB (e*g) hegB a j hja
      obtain ⟨c,d,hc,hlt⟩ := restricted_euclidean_descent ((e*g) j j) ((e*g) a j) hconst hb hmod
      let e' := E (Ne.symm haj) d * E haj c * e
      have he' : e' ∈ H := H.mul_mem (H.mul_mem
        (hE j a (Ne.symm haj) d (by intro h; exact False.elim (not_lt_of_ge hja h)))
        (hE a j haj c (by intro _; exact hc))) he
      have hpre' : ColumnPrefix (e'*g) j.val := by
        dsimp only [e']
        rw [mul_assoc,mul_assoc]
        exact columnPrefix_E_mul (columnPrefix_E_mul hpref haj le_rfl c) (Ne.symm haj) hja d
      have hpiv : (e'*g) j j = (e*g) j j + d*((e*g) a j + c*(e*g) j j) := by
        dsimp only [e']
        simp only [mul_assoc,E_mul_apply,ite_eq_right (Ne.symm haj),add_zero,ite_true]
      have hnew : P (((e*g) j j + d*((e*g) a j+c*(e*g) j j)).natDegree) :=
        ⟨e',he',hpre',by rw [hpiv]⟩
      apply Nat.find_min hex _ hnew
      simpa only [← hdegree] using hlt
  refine ⟨e,he,hpref,isUnit_of_dvd_one ?_⟩
  have hs := inverse_column_sum (e*g) j j
  rw [ite_eq_left rfl] at hs
  apply (show (e*g) j j ∣ ∑ a, (e*g)⁻¹ j a * (e*g) a j from ?_).trans (dvd_of_eq hs)
  apply Finset.dvd_sum
  intro a _
  by_cases hja : j ≤ a
  · exact dvd_mul_of_dvd_right (hdiv a hja) _
  · rw [inverse_prefix_zero (e*g) hpref (show a.val < j.val from lt_of_not_ge hja)
      (ne_of_gt (lt_of_not_ge hja)),zero_mul]
    exact dvd_zero _

theorem clear_column_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hgB : g ∈ B)
    (j : Fin n) (hg : ColumnPrefix g j.val) (hu : IsUnit (g j j)) :
    ∃ e ∈ H, ColumnPrefix (e*g) (j.val+1) := by
  classical
  obtain ⟨u,hu⟩ := hu
  have hclear : ∀ s : Finset (Fin n), (∀ a ∈ s, a ≠ j) →
      ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ (e*g) j j = (u : Polynomial F) ∧
        ∀ a ∈ s, (e*g) a j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1,H.one_mem,by simpa using hg,by simpa using hu.symm,by simp⟩
    | @insert a s has ih =>
      intro hs
      obtain ⟨e,he,hpref,hpiv,hz⟩ := ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      have haj : a ≠ j := hs a (Finset.mem_insert_self _ _)
      let c : Polynomial F := -((e*g) a j) * (↑(u⁻¹) : Polynomial F)
      have hc : E haj c ∈ H := by
        apply hE
        intro hja
        dsimp only [c]
        rw [map_mul,map_neg,hB (e*g) (B.mul_mem (hHB he) hgB) a j hja.le,ite_eq_right haj]
        simp
      refine ⟨E haj c * e,H.mul_mem hc he,?_,?_,?_⟩
      · rw [mul_assoc]
        exact columnPrefix_E_mul hpref haj le_rfl c
      · rw [mul_assoc,E_mul_apply,ite_eq_right (Ne.symm haj),add_zero,hpiv]
      · intro b hb
        rw [mul_assoc,E_mul_apply]
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [ite_eq_left rfl,hpiv]
          dsimp [c]
          rw [mul_assoc,Units.inv_mul,mul_one,add_neg_cancel]
        · rw [ite_eq_right (by intro h; subst b; exact has hb),add_zero]
          exact hz b hb
  obtain ⟨e,he,hpref,_,hz⟩ := hclear (Finset.univ.erase j) (by simp)
  refine ⟨e,he,?_⟩
  intro a b hb hab
  by_cases hbj : b.val < j.val
  · exact hpref a b hbj hab
  · have hbe : b=j := Fin.ext (by omega)
    subst b
    exact hz a (by simp [hab])

theorem diagonalize_polynomial_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hg : g ∈ B) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e*g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e*g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1,H.one_mem,by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e,he,hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k,by omega⟩
      have heg := B.mul_mem (hHB he) hg
      obtain ⟨h,hh,hpref',hpiv⟩ := exists_unit_pivot_iwahori B H hHB hB hE (e*g) heg j hpref
      obtain ⟨r,hr,hcol⟩ := clear_column_iwahori B H hHB hB hE (h*(e*g))
        (B.mul_mem (hHB hh) heg) j hpref' hpiv
      exact ⟨r*h*e,H.mul_mem (H.mul_mem hr hh) he,by simpa [mul_assoc,j] using hcol⟩
  obtain ⟨e,he,hpref⟩ := hsteps n le_rfl
  exact ⟨e,he,fun i j hij => hpref i j j.isLt hij⟩

theorem polynomial_iwahori_mem_of_roots
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hg : g ∈ B) : g ∈ H := by
  obtain ⟨e,he,hdiag⟩ := diagonalize_polynomial_iwahori B H hHB hB hE g hg
  have heg : e*g = 1 := by
    ext i j
    by_cases hij : i=j
    · subst j
      have hunit := column_diagonal_unit (e*g) i (fun a ha => hdiag a i ha)
      obtain ⟨c,hc,hc'⟩ := Polynomial.isUnit_iff.mp hunit
      have hconst := hB (e*g) (B.mul_mem (hHB he) hg) i i le_rfl
      rw [← hc'] at hconst
      have hc1 : c=1 := by simpa using hconst
      simp [← hc',hc1]
    · simp [hdiag i j hij, hij]
  rw [eq_inv_of_mul_eq_one_right heg]
  exact H.inv_mem he

end CoboundaryExpanders.Elementary

end

open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Mixing
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Small-set expansion, local spectral descent, connectedness, and uniform coset mixing.
-/

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Construction

section
open Elementary
variable (p n : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem cycleRoot_mem_generated (hn : 1 ≤ n) (j : Fin (n + 1)) :
    cycleRoot p n hn j ∈ cycleGenerated p n hn :=
  Subgroup.subset_closure ⟨j, rfl⟩

theorem cycleGenerated_le_U (hn : 1 ≤ n) : cycleGenerated p n hn ≤ U p (n + 1) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact cycleRoot_mem_U p n hn j

omit [Fact p.Prime] in
theorem upper_adjacent_mem_generated (hn : 1 ≤ n) (i j : Fin (n + 1))
    (hij : i.val + 1 = j.val) :
    E (show i ≠ j by intro he; subst j; omega) (1 : R p) ∈ cycleGenerated p n hn := by
  have hj : j ≠ 0 := by intro he; subst j; simp at hij
  have hs : edgeSource n j = i := by
    apply Fin.ext
    simp only [edgeSource, dite_eq_right hj, Fin.val_mk]
    omega
  simpa only [cycleRoot, ite_eq_right hj, hs] using cycleRoot_mem_generated p n hn j

omit [Fact p.Prime] in
theorem upper_one_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i < j) :
    E hij.ne (1 : R p) ∈ cycleGenerated p n hn :=
  E_upper_one_mem _ (upper_adjacent_mem_generated p n hn) hij

omit [Fact p.Prime] in
theorem lower_X_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : j < i) :
    E hij.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
  have hlast0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  have hbase : E hlast0 (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    simpa [cycleRoot, edgeSource, E] using
      cycleRoot_mem_generated p n hn 0
  have hlastj : j < Fin.last n := by change j.val < n; have := i.isLt; omega
  have hlast : E hlastj.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    by_cases hj : j = 0
    · subst j; exact hbase
    · have h0j : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj
      simpa only [mul_one] using E_path_mem (cycleGenerated p n hn)
        hlast0 h0j.ne hlastj.ne.symm hbase (upper_one_mem_generated p n hn h0j)
  by_cases hi : i = Fin.last n
  · subst i; exact hlast
  · have hilast : i < Fin.last n := by change i.val < n; have := i.isLt; have := Fin.ext_iff.not.mp hi; simp only [Fin.val_last] at this; omega
    simpa only [one_mul] using E_path_mem (cycleGenerated p n hn)
      hilast.ne hlastj.ne.symm hij.ne.symm (upper_one_mem_generated p n hn hilast) hlast

omit [Fact p.Prime] in
theorem X_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) :
    E hij (Polynomial.X : R p) ∈ cycleGenerated p n (by omega) := by
  have hn1 : 1 ≤ n := by omega
  by_cases hji : j < i
  · exact lower_X_mem_generated p n hn1 hji
  have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = Fin.last n
    · subst j
      let k : Fin (n + 1) := ⟨1, by omega⟩
      have h0k : (0 : Fin (n + 1)) < k := by change (0 : ℕ) < 1; omega
      have hklast : k < Fin.last n := by change 1 < n; omega
      have hk0 := lower_X_mem_generated p n hn1 h0k
      have h0last := upper_one_mem_generated p n hn1 hij'
      have hklastX : E hklast.ne (Polynomial.X : R p) ∈ cycleGenerated p n hn1 := by
        simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
          h0k.ne.symm hij'.ne hklast.ne hk0 h0last
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0k.ne hklast.ne hij (upper_one_mem_generated p n hn1 h0k) hklastX
    · have hjlast : j < Fin.last n := by
        change j.val < n
        have := j.isLt
        have := Fin.ext_iff.not.mp hj
        simp only [Fin.val_last] at this
        omega
      have h0last : (0 : Fin (n + 1)) < Fin.last n := by change 0 < n; omega
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0last.ne hjlast.ne.symm hij (upper_one_mem_generated p n hn1 h0last)
        (lower_X_mem_generated p n hn1 hjlast)
  · have h0i : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
    have h0j : (0 : Fin (n + 1)) < j := h0i.trans hij'
    simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
      h0i.ne.symm h0j.ne hij (lower_X_mem_generated p n hn1 h0i)
      (upper_one_mem_generated p n hn1 h0j)

omit [Fact p.Prime] in
theorem X_pow_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) (r : ℕ) :
    E hij (Polynomial.X ^ (r + 1) : R p) ∈ cycleGenerated p n (by omega) := by
  induction r generalizing i j with
  | zero => simpa only [zero_add, pow_one] using X_mem_generated p n hn hij
  | succ r ih =>
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    simpa only [pow_succ] using E_path_mem (cycleGenerated p n (by omega))
      hki.symm hkj hij (ih hki.symm) (X_mem_generated p n hn hkj)

theorem scalar_root_mem (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j)
    {f : R p} (hf : E hij f ∈ cycleGenerated p n hn) (c : ZMod p) :
    E hij (Polynomial.C c * f) ∈ cycleGenerated p n hn := by
  have hc : Polynomial.C c = (c.val : R p) := by
    calc Polynomial.C c = Polynomial.C (c.val : ZMod p) :=
           congrArg Polynomial.C (ZMod.natCast_zmod_val c).symm
         _ = _ := map_natCast Polynomial.C _
  rw [hc, E_natCast_mul]
  exact (cycleGenerated p n hn).pow_mem hf _

theorem upper_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i < j) (f : R p) : E hij.ne f ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    change Matrix.SpecialLinearGroup.transvection hij.ne (f + g) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    apply scalar_root_mem
    cases r with
    | zero => simpa using upper_one_mem_generated p n (by omega) hij
    | succ r => exact X_pow_mem_generated p n hn hij.ne r

theorem X_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i ≠ j) (f : R p) :
    E hij (Polynomial.X * f) ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [mul_add]
    change Matrix.SpecialLinearGroup.transvection hij (_ + _) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [mul_left_comm, ← pow_succ']
    exact scalar_root_mem p n (by omega) hij (X_pow_mem_generated p n hn hij r) c

end

open Elementary
variable (p n m : ℕ) [Fact p.Prime]

theorem map_E {A B : Type*} [CommRing A] [CommRing B] {a : ℕ}
    (φ : A →+* B) {i j : Fin a} (hij : i ≠ j) (c : A) :
    Matrix.SpecialLinearGroup.map φ (E hij c) = E hij (φ c) := by
  exact map_transvection φ hij c

theorem truncatedIwahori_entries (hm : 1 ≤ m)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m))
    (hg : g ∈ truncatedIwahori p n m hm) (i j : Fin (n + 1)) (hji : j ≤ i) :
    residue p m hm (g i j) = if i = j then 1 else 0 := by
  have := hg i j hji
  simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.one_apply] using this

theorem reduction_mem_truncatedIwahori (hm : 1 ≤ m)
    {g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)} (hg : g ∈ U p (n + 1)) :
    Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) g ∈
      truncatedIwahori p n m hm := by
  intro i j hji
  have := hg i j hji
  simpa [evalZero, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] using this

theorem reducedGenerated_le (hn : 1 ≤ n) (hm : 1 ≤ m) :
    reducedGenerated p n m hn ≤ truncatedIwahori p n m hm := by
  rintro _ ⟨g, hg, rfl⟩
  exact reduction_mem_truncatedIwahori p n m hm (cycleGenerated_le_U p n hn hg)

theorem reducedGenerated_roots (hn : 2 ≤ n) (hm : 1 ≤ m)
    (i j : Fin (n + 1)) (hij : i ≠ j) (c : Trunc p m)
    (hc : j < i → residue p m hm c = 0) :
    E hij c ∈ reducedGenerated p n m (by omega) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨E hij f, ?_, map_E _ hij f⟩
  by_cases hji : j < i
  · have hf : Polynomial.X ∣ f := Polynomial.X_dvd_iff.mpr (by
      have := hc hji
      simpa [Polynomial.coeff_zero_eq_eval_zero] using this)
    obtain ⟨b, rfl⟩ := hf
    exact X_polynomial_mem_generated p n hn hij b
  · exact upper_polynomial_mem_generated p n hn (lt_of_le_of_ne (le_of_not_gt hji) hij) f

theorem truncatedIwahori_eq_generated (hn : 2 ≤ n) (hm : 1 ≤ m) :
    truncatedIwahori p n m hm = reducedGenerated p n m (by omega) := by
  apply le_antisymm
  · exact iwahori_mem_of_roots (residue p m hm) _ _
      (reducedGenerated_le p n m (by omega) hm)
      (truncatedIwahori_entries p n m hm) (residue_one_isUnit p m hm)
      (reducedGenerated_roots p n m hn hm)
  · exact reducedGenerated_le p n m (by omega) hm

theorem quotient_locals_generate (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Subgroup.closure (⋃ i, (reducedLocalGroup p n (by omega) m i : Set (Gquot p (n + 1) m))) = ⊤ := by
  let K : Subgroup (Gquot p (n + 1) m) :=
    Subgroup.closure (⋃ i, (reducedLocalGroup p n (by omega) m i : Set (Gquot p (n + 1) m)))
  let e : Gquot p (n + 1) m →* Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m) :=
    QuotientGroup.kerLift (uReduction p (n + 1) m)
  have he : Function.Injective e := QuotientGroup.kerLift_injective _
  have hgen : reducedGenerated p n m (by omega) ≤ K.map e := by
    apply (Subgroup.map_le_iff_le_comap).mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨cut, hcut⟩ : ∃ cut : Fin (n + 1), cut ≠ j := by
      by_cases hj : j = 0
      · refine ⟨Fin.last n, ?_⟩
        rw [hj]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_zero] at this
        omega
      · exact ⟨0, fun h => hj h.symm⟩
    let u : U p (n + 1) := ⟨cycleRoot p n (by omega) j, cycleRoot_mem_U p n (by omega) j⟩
    have hu : u ∈ uLocalGroup p n (by omega) cut :=
      Subgroup.subset_closure ⟨j, hcut.symm, rfl⟩
    have hq : QuotientGroup.mk' (uReduction p (n + 1) m).ker u ∈ K :=
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨cut, ⟨u, hu, rfl⟩⟩)
    exact ⟨_, hq, rfl⟩
  apply top_le_iff.mp
  intro q _
  induction q using QuotientGroup.induction_on with
  | H u =>
    have hu := reduction_mem_truncatedIwahori p n m hm u.property
    rw [truncatedIwahori_eq_generated p n m hn hm] at hu
    obtain ⟨v, hv, hev⟩ := hgen hu
    have hveq : v = QuotientGroup.mk u := he hev
    exact hveq ▸ hv

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Odd-index transfer, comparison of bar resolutions, and homology-coinvariant models.
-/

section
open CategoryTheory
open scoped BigOperators

namespace CoboundaryExpanders.Transfer

section
open Representation

variable {k G V W : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

theorem inclusion_normTransfer :
    inclusion ρ S ∘ₗ normTransfer ρ S =
      (Fintype.card (G ⧸ S) : k) • LinearMap.id := by
  apply Coinvariants.hom_ext
  ext v
  simp [LinearMap.comp_apply, map_sum, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

end

universe u
variable {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

theorem chainTransfer_inclusion (C : ChainComplex (Rep k G) ℕ)
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) :
    chainTransfer S C ≫ chainInclusion S C = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  change inclusion (C.X n).ρ S ∘ₗ normTransfer (C.X n).ρ S = LinearMap.id
  simpa only [hindex, one_smul] using inclusion_normTransfer (C.X n).ρ S

theorem homology_chainInclusion_surjective (C : ChainComplex (Rep k G) ℕ)
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap (chainInclusion S C) j) := by
  have hh : HomologicalComplex.homologyMap (chainTransfer S C) j ≫
      HomologicalComplex.homologyMap (chainInclusion S C) j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, chainTransfer_inclusion S C hindex,
      HomologicalComplex.homologyMap_id]
  intro y
  refine ⟨HomologicalComplex.homologyMap (chainTransfer S C) j y, ?_⟩
  exact congrArg (fun f => ModuleCat.Hom.hom f y) hh

end CoboundaryExpanders.Transfer

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.Transfer

section
open CategoryTheory Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

omit [S.Normal] [Fintype (G ⧸ S)] in
theorem chain_factorization :
    CoinvariantModel.chainsIso.hom ≫ barCoinvariantInclusion (k := k) S ≫
      chainInclusion S (Rep.barComplex k G) =
    groupHomology.chainsMap S.subtype (trivialInclusion (k := k) S) ≫
      (CoinvariantModel.chainsIso (k := k) (G := G)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change inclusion (Representation.free k G (Fin n → G)) S
    (Representation.Coinvariants.map _ _ (BarComparison.inclusionF (k := k) S n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n (single x r))) =
    (CoinvariantModel.chainsIso (k := k) (G := G)).hom.f n
      ((groupHomology.chainsMap S.subtype (trivialInclusion (k := k) S)).f n (single x r))
  rw [CoinvariantModel.chainsIso_hom_single, Coinvariants.map_mk,
    BarComparison.inclusionF_single, inclusion_mk,
    groupHomology.chainsMap_f_single, CoinvariantModel.chainsIso_hom_single]
  rfl

theorem homology_surjective_of_homotopyEquiv
    {C D : ChainComplex (ModuleCat k) ℕ} (e : HomotopyEquiv C D) (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap e.hom j) := by
  have h : HomologicalComplex.homologyMap e.inv j ≫
      HomologicalComplex.homologyMap e.hom j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      e.homotopyInvHomId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  intro y
  refine ⟨HomologicalComplex.homologyMap e.inv j y, ?_⟩
  exact congrArg (fun f => ModuleCat.Hom.hom f y) h

omit [DecidableEq G] [S.Normal] [Fintype (G ⧸ S)] in
theorem homology_barCoinvariantInclusion_surjective (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap
      (barCoinvariantInclusion (k := k) S) j) :=
  homology_surjective_of_homotopyEquiv
    ((Rep.coinvariantsFunctor k S).mapHomotopyEquiv (BarComparison.inclusionEquiv S)) j

theorem groupHomology_inclusion_surjective
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ) :
    Function.Surjective
      (groupHomology.map S.subtype (trivialInclusion (k := k) S) j) := by
  let eS := CoinvariantModel.chainsIso (k := k) (G := S)
  let eG := CoinvariantModel.chainsIso (k := k) (G := G)
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
    (chain_factorization (k := k) S)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  intro y
  obtain ⟨b, hb⟩ := homology_chainInclusion_surjective S (Rep.barComplex k G) hindex j
    (HomologicalComplex.homologyMap eG.hom j y)
  obtain ⟨c, hc⟩ := homology_barCoinvariantInclusion_surjective (k := k) S j b
  obtain ⟨z, hz⟩ := homology_surjective_of_homotopyEquiv (HomotopyEquiv.ofIso eS) j c
  refine ⟨z, ?_⟩
  have hi : Function.Injective (HomologicalComplex.homologyMap eG.hom j) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hi
  have he := congrArg (fun f => ModuleCat.Hom.hom f z) hf
  change HomologicalComplex.homologyMap (chainInclusion S (Rep.barComplex k G)) j
    (HomologicalComplex.homologyMap (barCoinvariantInclusion (k := k) S) j
      (HomologicalComplex.homologyMap eS.hom j z)) =
    HomologicalComplex.homologyMap eG.hom j
      (groupHomology.map S.subtype (trivialInclusion (k := k) S) j z) at he
  change HomologicalComplex.homologyMap eS.hom j z = c at hz
  rw [hz, hc, hb] at he
  exact he.symm

variable {H : Type u} [Group H]

omit [DecidableEq G] in
theorem homology_equiv_surjective (e : H ≃* G) (j : ℕ) :
    Function.Surjective
      (groupHomology.map e.toMonoidHom (trivialCoefficients (k := k) e.toMonoidHom) j) := by
  let E := groupHomology.mapIso (A := Rep.trivial k H k) (B := Rep.trivial k G k)
    e (LinearEquiv.refl k k) (fun _ => rfl) j
  have he : groupHomology.map e.toMonoidHom
      (trivialCoefficients (k := k) e.toMonoidHom) j = E.hom := by
    exact groupHomology.map_congr rfl rfl j
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso E.hom).surjective

theorem nested_subgroup_inclusion_surjective (H K : Subgroup G) (hHK : H ≤ K)
    [(H.subgroupOf K).Normal] [Fintype (K ⧸ H.subgroupOf K)]
    (hindex : (Fintype.card (K ⧸ H.subgroupOf K) : k) = 1) (j : ℕ) :
    Function.Surjective (groupHomology.map (Subgroup.inclusion hHK)
      (trivialCoefficients (k := k) (Subgroup.inclusion hHK)) j) := by
  let e := (Subgroup.subgroupOfEquivOfLe hHK).symm
  have he := homology_equiv_surjective (k := k) e j
  have hi := groupHomology_inclusion_surjective (k := k) (H.subgroupOf K) hindex j
  have hcomp : groupHomology.map (Subgroup.inclusion hHK)
      (trivialCoefficients (k := k) (Subgroup.inclusion hHK)) j =
      groupHomology.map e.toMonoidHom (trivialCoefficients (k := k) e.toMonoidHom) j ≫
      groupHomology.map (H.subgroupOf K).subtype
        (trivialInclusion (k := k) (H.subgroupOf K)) j := by
    rw [← groupHomology.map_comp]
    exact groupHomology.map_congr rfl rfl j
  rw [hcomp]
  exact hi.comp he

end

open Representation
universe u
variable {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

theorem normTransfer_inclusion (V : Type*) [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    normTransfer ρ S ∘ₗ inclusion ρ S = ∑ q : G ⧸ S, ρ.quotientToCoinvariants S q := by
  apply Coinvariants.hom_ext
  ext v
  simp [LinearMap.comp_apply, LinearMap.sum_apply]

theorem chainInclusion_transfer (C : ChainComplex (Rep k G) ℕ) :
    chainInclusion S C ≫ chainTransfer S C = ∑ q : G ⧸ S, chainQuotientAction S C q := by
  apply HomologicalComplex.hom_ext
  intro n
  have hsum : (∑ q : G ⧸ S, chainQuotientAction (k := k) S C q).f n =
      ∑ q : G ⧸ S, (chainQuotientAction S C q).f n :=
    map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _
  rw [hsum]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  change normTransfer (C.X n).ρ S ∘ₗ inclusion (C.X n).ρ S =
    ∑ q : G ⧸ S, (C.X n).ρ.quotientToCoinvariants S q
  exact normTransfer_inclusion S _ _

theorem homology_chainInclusion_injective (C : ChainComplex (Rep k G) ℕ)
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (htriv : ∀ q, HomologicalComplex.homologyMap (chainQuotientAction S C q) j = 𝟙 _) :
    Function.Injective (HomologicalComplex.homologyMap (chainInclusion S C) j) := by
  have hh : HomologicalComplex.homologyMap (chainInclusion S C) j ≫
      HomologicalComplex.homologyMap (chainTransfer S C) j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, chainInclusion_transfer]
    change (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) j).map
      (∑ q : G ⧸ S, chainQuotientAction S C q) = _
    rw [Functor.map_sum]
    change (∑ q : G ⧸ S, HomologicalComplex.homologyMap (chainQuotientAction S C q) j) = _
    simp only [htriv, Finset.sum_const, Finset.card_univ]
    ext v
    change (Fintype.card (G ⧸ S)) • v = v
    rw [← Nat.cast_smul_eq_nsmul k, hindex, one_smul]
  intro x y hxy
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hh
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hh
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap (chainTransfer S C) j) hxy).trans hy)

end CoboundaryExpanders.Transfer

namespace CoboundaryExpanders.Transfer
open Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

omit [DecidableEq G] [S.Normal] [Fintype (G ⧸ S)] in
theorem homology_adjusted (g : G) (j : ℕ) :
    HomologicalComplex.homologyMap (barCoinvariantAdjusted (k := k) S g) j =
      HomologicalComplex.homologyMap (barCoinvariantInclusion (k := k) S) j :=
  ((Rep.coinvariantsFunctor k S).mapHomotopy (BarComparison.adjustedHomotopy S g)).homologyMap_eq j

omit [Fintype (G ⧸ S)] in
theorem chain_conjugation_factorization (g : G) :
    (CoinvariantModel.chainsIso (k := k) (G := S)).hom ≫ barCoinvariantAdjusted S g ≫
      chainQuotientAction S (Rep.barComplex k G) (g : G ⧸ S) =
    groupHomology.chainsMap (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) ≫
      (CoinvariantModel.chainsIso (k := k) (G := S)).hom ≫ barCoinvariantInclusion S := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change (Representation.free k G (Fin n → G)).quotientToCoinvariants S (g : G ⧸ S)
    (Coinvariants.map _ _ (BarComparison.adjustedF (k := k) S g n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n (single x r))) =
    Coinvariants.map _ _ (BarComparison.inclusionF (k := k) S n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n
        ((groupHomology.chainsMap (MulAut.conjNormal (H := S) g).toMonoidHom
          (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom)).f n (single x r)))
  rw [CoinvariantModel.chainsIso_hom_single, Coinvariants.map_mk,
    BarComparison.adjustedF_single, quotient_action_mk,
    Representation.free_single_single,
    groupHomology.chainsMap_f_single, CoinvariantModel.chainsIso_hom_single,
    Coinvariants.map_mk, BarComparison.inclusionF_single]
  simp only [Subgroup.coe_one, one_mul, mul_inv_cancel]
  rfl

omit [Fintype (G ⧸ S)] in
theorem homology_quotientAction_eq_id (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _) :
    ∀ q : G ⧸ S, HomologicalComplex.homologyMap
      (chainQuotientAction S (Rep.barComplex k G) q) j = 𝟙 _ := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
      (chain_conjugation_factorization (k := k) S g)
    simp only [HomologicalComplex.homologyMap_comp, homology_adjusted] at hf
    change HomologicalComplex.homologyMap CoinvariantModel.chainsIso.hom j ≫
      HomologicalComplex.homologyMap (barCoinvariantInclusion S) j ≫
      HomologicalComplex.homologyMap (chainQuotientAction S (Rep.barComplex k G) (g : G ⧸ S)) j =
      groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
        (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j ≫
      HomologicalComplex.homologyMap CoinvariantModel.chainsIso.hom j ≫
      HomologicalComplex.homologyMap (barCoinvariantInclusion S) j at hf
    rw [hconj, Category.id_comp] at hf
    have hs := (homology_barCoinvariantInclusion_surjective (k := k) S j).comp
      (homology_surjective_of_homotopyEquiv
        (HomotopyEquiv.ofIso (CoinvariantModel.chainsIso (k := k) (G := S))) j)
    ext v
    obtain ⟨x, rfl⟩ := hs v
    exact congrArg (fun f => ModuleCat.Hom.hom f x) hf

theorem homology_injective_of_homotopyEquiv
    {C D : ChainComplex (ModuleCat k) ℕ} (e : HomotopyEquiv C D) (j : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap e.hom j) := by
  have hh : HomologicalComplex.homologyMap e.hom j ≫
      HomologicalComplex.homologyMap e.inv j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      e.homotopyHomInvId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  intro x y hxy
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hh
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hh
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap e.inv j) hxy).trans hy)

theorem groupHomology_inclusion_injective
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _) :
    Function.Injective
      (groupHomology.map S.subtype (trivialInclusion (k := k) S) j) := by
  have hi := homology_chainInclusion_injective S (Rep.barComplex k G) hindex j
    (homology_quotientAction_eq_id S j hconj)
  have hb := homology_injective_of_homotopyEquiv
    ((Rep.coinvariantsFunctor k S).mapHomotopyEquiv (BarComparison.inclusionEquiv S)) j
  have hs := homology_injective_of_homotopyEquiv
    (HomotopyEquiv.ofIso (CoinvariantModel.chainsIso (k := k) (G := S))) j
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
    (chain_factorization (k := k) S)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  intro x y hxy
  apply hs
  apply hb
  apply hi
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hf
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hf
  exact hx.trans ((congrArg
    (HomologicalComplex.homologyMap (CoinvariantModel.chainsIso (k := k) (G := G)).hom j)
    hxy).trans hy.symm)

theorem subgroup_homology_isZero_of_conjugation
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _)
    (hzero : Limits.IsZero (groupHomology (Rep.trivial k G k) j)) :
    Limits.IsZero (groupHomology (Rep.trivial k S k) j) := by
  let f := groupHomology.map S.subtype (trivialInclusion (k := k) S) j
  have : Mono f := (ModuleCat.mono_iff_injective f).mpr
    (groupHomology_inclusion_injective S hindex j hconj)
  exact Limits.IsZero.of_mono f hzero

end CoboundaryExpanders.Transfer

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Coinvariants
attribute [-instance] _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Simplicial group actions, permutation modules, coset sums, and chain coinvariants.
-/

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra

namespace CoboundaryExpanders.TypedCosetFaces

section
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

omit [DecidableEq I] in
lemma stabilizer_le (A : Finset I) {i : I} (hi : i ∈ A) : stabilizer H A ≤ H i :=
  fun _ hg => (mem_stabilizer H A _).mp hg i hi

omit [DecidableEq I] in
lemma stabilizer_finite [∀ i, Finite (H i)] (A : Finset I) (hA : A.Nonempty) :
    Finite (stabilizer H A) := by
  obtain ⟨i,hi⟩ := hA
  exact Finite.of_injective (Subgroup.inclusion (stabilizer_le H A hi))
    (Subgroup.inclusion_injective _)

omit [DecidableEq I] in
lemma stabilizer_odd (hH : ∀ i, Odd (Nat.card (H i))) (A : Finset I) (hA : A.Nonempty) :
    Odd (Nat.card (stabilizer H A)) := by
  obtain ⟨i,hi⟩ := hA
  exact (hH i).of_dvd_nat (Subgroup.card_dvd_of_le (stabilizer_le H A hi))

theorem projective_chains [∀ i, Finite (H i)] (hH : ∀ i, Odd (Nat.card (H i))) (j : ℕ) :
    Projective (((complex H).repComplex (G := G)).X j) := by
  let _ : ∀ A : Types (I := I) (j+1), Finite (stabilizer H A.val) :=
    fun A => stabilizer_finite H A.val (Finset.card_pos.mp (by omega))
  have hp := CosetSums.projective_of_odd_order
    (fun A : Types (I := I) (j+1) => stabilizer H A.val)
    (fun A => stabilizer_odd H hH A.val (Finset.card_pos.mp (by omega)))
  exact Projective.of_iso (chainsIso H (j+1)) hp

end

open InfiniteChains
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

theorem coinvariant_homology_isZero [Nonempty I] (j : ℕ) :
    Limits.IsZero ((coinvariantComplex H).homology (j+1)) := by
  let a : I := Classical.choice inferInstance
  have hz := (Simplex (I := I)).chainComplex_homology_isZero_of_cone a
    (CoboundaryExpanders.InfiniteChains.Complex.full_isConePoint a) j
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ (j+1)).mapIso
    (coinvariantSimplexIso H))

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Stabilization
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Block stabilization, homology actions, quotient vanishing, and congruence cokernels.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Blocks

open CoboundaryExpanders.Elementary CoboundaryExpanders.Construction
variable {A : Type*} [CommRing A]

theorem stabilize_commutes_tail (a b : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A)
    {i j : Fin b} (hij : i ≠ j) (c : A) :
    Commute (E (show Fin.natAdd a i ≠ Fin.natAdd a j from
      fun he => hij (Fin.ext (by have := congrArg Fin.val he; simpa using this))) c)
      (stabilizeSL a b g) := by
  apply elementary_commutes_of_complement
  · exact stabilizeSL_right_row a b g j
  · exact fun k => stabilizeSL_right_col a b g k i

theorem exists_pair_permutation (a : ℕ) (i j : Fin (a + 2)) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin (a + 2)), e (Fin.natAdd a 0) = i ∧ e (Fin.natAdd a 1) = j := by
  classical
  let f : Fin 2 → Fin (a + 2) := Fin.natAdd a
  let g : Fin 2 → Fin (a + 2) := fun x => if x = 0 then i else j
  have hf : Function.Injective f := by
    intro x y h
    apply Fin.ext
    have he := congrArg Fin.val h
    change a + x.val = a + y.val at he
    omega
  have hg : Function.Injective g := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [g]
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨e, by simpa [f, g] using he 0, by simpa [f, g] using he 1⟩

theorem elementary_centralizes_complement (p a m : ℕ) (i j : Fin (a + 2))
    (hij : i ≠ j) (c : R p) :
    ∃ e : Equiv.Perm (Fin (a + 2)), ∀ x : Gamma p a m,
      Commute (E hij c)
        ((gammaReindex p (a + 2) m e (gammaStabilization p a 2 m x)).val) := by
  obtain ⟨e, hi, hj⟩ := exists_pair_permutation a i j hij
  refine ⟨e, fun x => ?_⟩
  have hc := stabilize_commutes_tail a 2 x.val (show (0 : Fin 2) ≠ 1 by decide) c
  have hm := hc.map (reindexSL e).toMonoidHom
  change Commute (reindexSL e (E _ c)) (reindexSL e (stabilizeSL a 2 x.val)) at hm
  rw [reindexSL_E] at hm
  change Commute (E hij c) (reindexSL e (stabilizeSL a 2 x.val))
  simpa only [hi, hj] using hm

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Actions
universe u
variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]

theorem induced_equiv_surjective (e : H ≃* G) (j : ℕ) :
    Function.Surjective (induced (k := k) e.toMonoidHom j) := by
  have he := induced_comp (k := k) e.symm.toMonoidHom e.toMonoidHom j
  have hc : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [hc, induced_id] at he
  intro x
  refine ⟨induced e.symm.toMonoidHom j x, ?_⟩
  exact (congrArg (fun f => ModuleCat.Hom.hom f x) he).symm

variable (S : Subgroup G) [S.Normal]

theorem centralizer_fixes_image (φ : H →* S) (g : G)
    (hcomm : ∀ x : H, Commute g ((φ x : S) : G)) (j : ℕ) :
    induced (k := k) φ j ≫ conjugation S g j = induced φ j := by
  unfold conjugation
  rw [← induced_comp]
  apply induced_congr
  ext x
  change g * (φ x : G) * g⁻¹ = (φ x : G)
  rw [(hcomm x).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem centralizer_fixes_of_surjective (φ : H →* S) (g : G)
    (hcomm : ∀ x : H, Commute g ((φ x : S) : G)) (j : ℕ)
    (hsurj : Function.Surjective (induced (k := k) φ j)) :
    g ∈ fixingSubgroup (k := k) S j := by
  change conjugation S g j = 𝟙 _
  have he := centralizer_fixes_image (k := k) S φ g hcomm j
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact congrArg (fun f => ModuleCat.Hom.hom f y) he

end CoboundaryExpanders.Actions

namespace CoboundaryExpanders.Blocks
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
open CoboundaryExpanders.Actions CategoryTheory

theorem trivial_action_of_stabilization (p a m r : ℕ) [Fact p.Prime]
    (hsurj : Function.Surjective (induced (k := ZMod 2) (gammaStabilization p a 2 m) r))
    (g : Matrix.SpecialLinearGroup (Fin (a + 2)) (R p)) :
    conjugation (k := ZMod 2) (Gamma p (a + 2) m) g r = 𝟙 _ := by
  change g ∈ fixingSubgroup (k := ZMod 2) (Gamma p (a + 2) m) r
  apply polynomial_SL_mem_of_roots
  intro i j hij c
  obtain ⟨e, he⟩ := elementary_centralizes_complement p a m i j hij c
  apply centralizer_fixes_of_surjective (Gamma p (a + 2) m)
    ((gammaReindex p (a + 2) m e).toMonoidHom.comp (gammaStabilization p a 2 m)) (E hij c) he r
  rw [induced_comp]
  exact (induced_equiv_surjective (k := ZMod 2) (gammaReindex p (a + 2) m e) r).comp hsurj

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.QuotientVanishing
open CategoryTheory CoboundaryExpanders.Construction CoboundaryExpanders.Actions

variable (p a m : ℕ) [NeZero p]

theorem gammaInU_conj (hm : 1 ≤ m) (g : U p a) :
    (MulAut.conjNormal (H := K p a m) g).toMonoidHom.comp (gammaInU p a m hm).toMonoidHom =
    (gammaInU p a m hm).toMonoidHom.comp (MulAut.conjNormal (H := Gamma p a m) g.val).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem conjugation_in_U (hm : 1 ≤ m) (j : ℕ)
    (hconj : ∀ g : Matrix.SpecialLinearGroup (Fin a) (R p),
      conjugation (k := ZMod 2) (Gamma p a m) g j = 𝟙 _) (g : U p a) :
    conjugation (k := ZMod 2) (K p a m) g j = 𝟙 _ := by
  have hh := induced_congr (k := ZMod 2) (gammaInU_conj p a m hm g) j
  rw [induced_comp, induced_comp] at hh
  change induced (gammaInU p a m hm).toMonoidHom j ≫ conjugation (K p a m) g j =
    conjugation (Gamma p a m) g.val j ≫ induced (gammaInU p a m hm).toMonoidHom j at hh
  rw [hconj, Category.id_comp] at hh
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := induced_equiv_surjective (k := ZMod 2) (gammaInU p a m hm) j x
  exact congrArg (fun f => ModuleCat.Hom.hom f y) hh

theorem gamma_isZero_of_U_and_action (hp : p.Prime) (hodd : Odd p)
    (hm : 1 ≤ m) (j : ℕ)
    (hU : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p a) (ZMod 2)) j))
    (hconj : ∀ g : Matrix.SpecialLinearGroup (Fin a) (R p),
      conjugation (k := ZMod 2) (Gamma p a m) g j = 𝟙 _) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  have : Finite (U p a ⧸ K p a m) := inferInstanceAs (Finite (Gquot p a m))
  let : Fintype (U p a ⧸ K p a m) := Fintype.ofFinite _
  have hindex : (Fintype.card (U p a ⧸ K p a m) : ZMod 2) = 1 := by
    have h := odd_gquot_card p a m hp hodd
    change Odd (Nat.card (U p a ⧸ K p a m)) at h
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨r, hr⟩ := h
    rw [hr]
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, htwo, zero_mul, zero_add]
  have hz : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (K p a m) (ZMod 2)) j) := by
    apply Transfer.subgroup_homology_isZero_of_conjugation (K p a m) hindex j
    · intro g
      exact conjugation_in_U p a m hm j hconj g
    · exact hU
  let f := induced (k := ZMod 2) (gammaInU p a m hm).symm.toMonoidHom j
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    (induced_equiv_surjective (k := ZMod 2) (gammaInU p a m hm).symm j)
  exact Limits.IsZero.of_epi f hz

theorem gamma_isZero_of_U_and_stabilization (hp : p.Prime) (hodd : Odd p)
    (hm : 1 ≤ m) (j : ℕ)
    (hU : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p (a + 2)) (ZMod 2)) j))
    (hst : Function.Surjective
      (induced (k := ZMod 2) (Blocks.gammaStabilization p a 2 m) j)) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a + 2) m) (ZMod 2)) j) := by
  have : Fact p.Prime := ⟨hp⟩
  apply gamma_isZero_of_U_and_action p (a + 2) m hp hodd hm j hU
  exact Blocks.trivial_action_of_stabilization p a m j hst

end CoboundaryExpanders.QuotientVanishing

namespace CoboundaryExpanders.Construction
open CategoryTheory

theorem congruence_homology_transition_surjective
    (p a m n : ℕ) (hp : p.Prime) (hodd : Odd p) (hm : 1 ≤ m) (hmn : m ≤ n)
    (j : ℕ) : Function.Surjective
      (groupHomology.map (Subgroup.inclusion (gamma_antitone p a hmn))
        (CoboundaryExpanders.Transfer.trivialCoefficients (k := ZMod 2)
          (Subgroup.inclusion (gamma_antitone p a hmn))) j) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : ((Gamma p a n).subgroupOf (Gamma p a m)).Normal := normalDeeper p a m n
  have : Finite (Gamma p a m ⧸ (Gamma p a n).subgroupOf (Gamma p a m)) :=
    finiteCongruenceQuotient p a m n
  let := Fintype.ofFinite (Gamma p a m ⧸ (Gamma p a n).subgroupOf (Gamma p a m))
  apply CoboundaryExpanders.Transfer.nested_subgroup_inclusion_surjective
  have ho := odd_congruence_index p a m n hp hodd hm
  rw [deeperCongruence_eq, Nat.card_eq_fintype_card] at ho
  obtain ⟨r, hr⟩ := ho
  rw [hr]
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [Nat.cast_add, Nat.cast_mul, htwo]

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Blocks

variable {A : Type*} [CommRing A]

theorem stabilizeSL_entry (a b : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin a) A) (i j : Fin (a + b)) :
    stabilizeSL a b g i j =
      if hi : i.val < a then
        if hj : j.val < a then g ⟨i.val, hi⟩ ⟨j.val, hj⟩ else (1 : Matrix _ _ A) i j
      else (1 : Matrix _ _ A) i j := by
  by_cases hi : i.val < a
  · rw [dite_eq_left hi]
    by_cases hj : j.val < a
    · rw [dite_eq_left hj]
      exact stabilizeSL_left_block a b g ⟨i.val, hi⟩ ⟨j.val, hj⟩
    · rw [dite_eq_right hj]
      let j' : Fin b := ⟨j.val - a, by omega⟩
      have hj' : j = Fin.natAdd a j' := by apply Fin.ext; dsimp [j']; omega
      rw [hj', stabilizeSL_right_col]
  · rw [dite_eq_right hi]
    let i' : Fin b := ⟨i.val - a, by omega⟩
    have hi' : i = Fin.natAdd a i' := by apply Fin.ext; dsimp [i']; omega
    rw [hi', stabilizeSL_right_row]

theorem stabilizeSL_two (a : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A) :
    stabilizeSL (a + 1) 1 (stabilizeSL a 1 g) = stabilizeSL a 2 g := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rw [stabilizeSL_entry, stabilizeSL_entry]
  by_cases hi : i.val < a + 1
  · rw [dite_eq_left hi]
    by_cases hj : j.val < a + 1
    · rw [dite_eq_left hj, stabilizeSL_entry]
      simp only [Fin.val_mk, Matrix.one_apply, Fin.ext_iff]
    · rw [dite_eq_right hj]
      by_cases hi' : i.val < a
      · rw [dite_eq_left hi', dite_eq_right (by omega : ¬ j.val < a)]
      · rw [dite_eq_right hi']
  · rw [dite_eq_right hi, dite_eq_right (by omega : ¬ i.val < a)]

open CoboundaryExpanders.Construction

theorem gammaStabilization_two (p a m : ℕ) :
    (gammaStabilization p (a + 1) 1 m).comp (gammaStabilization p a 1 m) =
      gammaStabilization p a 2 m := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.comp_apply, gammaStabilization_coe, stabilizeSL_two]

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Cokernel
variable {k : Type*} [CommRing k]
variable {A A' B B' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
  [Module k A] [Module k A'] [Module k B] [Module k B']

theorem transition_surjective (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u)
    (hv : Function.Surjective v) : Function.Surjective (transition f f' u v h) := by
  intro x
  obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective (LinearMap.range f)) x
  obtain ⟨y, rfl⟩ := hv x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem surjective_iff_coker_subsingleton (f : A →ₗ[k] B) :
    Function.Surjective f ↔ Subsingleton (Coker f) :=
  LinearMap.range_eq_top.symm.trans Submodule.Quotient.subsingleton_iff.symm

theorem surjective_of_zero_coker_transition
    (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u)
    (hv : Function.Surjective v)
    (hz : transition f f' u v h = 0) : Function.Surjective f := by
  apply (surjective_iff_coker_subsingleton f).mpr
  have hs := transition_surjective f f' u v h hv
  have he : ∀ x : Coker f, x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    rw [hz]; rfl
  exact ⟨fun x y => (he x).trans (he y).symm⟩

end CoboundaryExpanders.Cokernel

namespace CoboundaryExpanders.CongruenceCokernels
open CoboundaryExpanders.Construction CoboundaryExpanders.Blocks
open CoboundaryExpanders.Actions CategoryTheory

theorem transition_surjective (p a m n j : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m) (hmn : m ≤ n) :
    Function.Surjective (transition p a m n j hmn) := by
  exact congruence_homology_transition_surjective p a m n hp hodd hm hmn j

theorem stabilization_surjective_of_proZero (p a m j : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m) (hz : ProZero p a j) :
    Function.Surjective (stabilization p a m j) := by
  obtain ⟨n, hmn, hn⟩ := hz m hm
  apply Cokernel.surjective_of_zero_coker_transition
    (stabilization p a m j) (stabilization p a n j)
    (transition p a m n j hmn) (transition p (a + 1) m n j hmn)
    (natural p a m n j hmn)
  · exact transition_surjective p (a + 1) m n j hp hodd hm hmn
  · exact hn

theorem two_step_surjective_of_proZero (p a m j : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m) (hz : ProZero p a j) (hz' : ProZero p (a + 1) j) :
    Function.Surjective (induced (k := ZMod 2) (gammaStabilization p a 2 m) j) := by
  have hh := induced_congr (k := ZMod 2) (gammaStabilization_two p a m) j
  rw [induced_comp] at hh
  rw [← hh]
  exact (stabilization_surjective_of_proZero p (a + 1) m j hp hodd hm hz').comp
    (stabilization_surjective_of_proZero p a m j hp hodd hm hz)

theorem gamma_isZero_of_U_and_proZero (p a m j : ℕ) [NeZero p] (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m)
    (hU : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p (a + 2)) (ZMod 2)) j))
    (hz : ProZero p a j) (hz' : ProZero p (a + 1) j) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a + 2) m) (ZMod 2)) j) := by
  exact QuotientVanishing.gamma_isZero_of_U_and_stabilization p a m hp hodd hm j hU
    (two_step_surjective_of_proZero p a m j hp hodd hm hz hz')

end CoboundaryExpanders.CongruenceCokernels

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Resolution
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Partial resolutions, orbit projectivity, and homology of finite congruence coset complexes.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.TypedCosetFaces
open CategoryTheory
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq G] [DecidableEq I] [Nonempty I]
  (H : I → Subgroup G)

theorem groupHomology_isZero_of_acyclic [∀ i, Finite (H i)]
    (hodd : ∀ i, Odd (Nat.card (H i))) (h : ℕ)
    (hexact : ∀ n, n < h → (complex H).chainComplex.ExactAt (n+1))
    (hzero : Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1))
    (j : ℕ) (hj : j+1 ≤ h) :
    Limits.IsZero (groupHomology (Rep.trivial k G k) (j+1)) := by
  let a : I := Classical.choice inferInstance
  let _ : Nonempty ((complex H).Face 1) :=
    ⟨baseFace H 1 ⟨{a},Set.mem_univ _,by simp⟩⟩
  let ε : ((complex H).repComplex (G := G)).X 0 ⟶ Rep.trivial k G k :=
    (complex H).augmentationRep
  let _ : Epi ε := (complex H).augmentationRep_epi
  have hε : ((complex H).repComplex (G := G)).d 1 0 ≫ ε = 0 := by
    change (complex H).boundaryRep 1 ≫ (complex H).augmentationRep = 0
    exact (complex H).augmentationRep_boundary
  have hz : (ShortComplex.mk (((complex H).repComplex (G := G)).d 1 0)
      ε hε).Exact := by
    change (ShortComplex.mk ((complex H).boundaryRep 1)
      (complex H).augmentationRep _).Exact
    exact (complex H).augmentationRep_exact hzero
  let e := CoinvariantHomology.homologyIso k G ((complex H).repComplex (G := G)) h
    ε hε
    (fun n _ => projective_chains H hodd n)
    (fun n hn => (complex H).repComplex_exactAt n (hexact n hn)) hz (j+1) hj
  exact (coinvariant_homology_isZero H j).of_iso e

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open CategoryTheory InfiniteChains
variable (p n : ℕ) [Fact p.Prime]

lemma uLocalGroup_odd (hn : 1 ≤ n) (hp : Odd p) (i : Fin (n+1)) :
    Odd (Nat.card (uLocalGroup p n hn i)) := by
  let f : uLocalGroup p n hn i →* localGroup p n hn i :=
    { toFun := uLocalEmbedding p n hn i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (localGroup_odd p n hn hp i).of_dvd_nat
    (Subgroup.card_dvd_of_injective f (uLocalEmbedding p n hn i).injective)

theorem u_homology_isZero_of_opposition (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (j : ℕ) (hj : 0 < j) (hjn : j < n-1) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p (n+1)) (ZMod 2)) j) := by
  classical
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  apply TypedCosetFaces.groupHomology_isZero_of_acyclic (uLocalGroup p n (by omega))
    (uLocalGroup_odd p n (by omega) hp) (n-2)
  · intro r hr
    exact hL.2 (r+1) (by omega) (by omega)
  · exact hL.1
  · omega

theorem gamma_isZero_of_opposition_and_proZero (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (m j : ℕ)
    (hm : 1 ≤ m) (hj : 0 < j) (hjn : j < n-1)
    (hz : CongruenceCokernels.ProZero p (n-1) j)
    (hz' : CongruenceCokernels.ProZero p n j) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n+1) m) (ZMod 2)) j) := by
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, n = a+2 := ⟨n-2, by omega⟩
  have hU := u_homology_isZero_of_opposition p (a+2) hn hp hL j hj hjn
  exact CongruenceCokernels.gamma_isZero_of_U_and_proZero p (a+1) m j Fact.out hp hm
    hU (by simpa using hz) (by simpa only [Nat.add_assoc] using hz')

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Construction
open CategoryTheory TypedCosetFaces
variable (p n : ℕ) [Fact p.Prime]

theorem quotientTyped_homology_isZero (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (m j : ℕ)
    (hm : 2 ≤ m) (hj : 0 < j) (hjn : j < n-1)
    (hz : CongruenceCokernels.ProZero p (n-1) j)
    (hz' : CongruenceCokernels.ProZero p n j) :
    Limits.IsZero ((quotientTypedComplex p n (by omega) m).chainComplex.homology j) := by
  classical
  have hΓ := gamma_isZero_of_opposition_and_proZero p n hn hp hL m j (by omega) hj hjn hz hz'
  let e := gammaQuotientKernelEquiv p n m (by omega)
  let f := Actions.induced (k := ZMod 2) e.toMonoidHom j
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    (Actions.induced_equiv_surjective (k := ZMod 2) e j)
  have hk := Limits.IsZero.of_epi f hΓ
  exact hk.of_iso (matrixKernelHomologyIso p n hn m hm hL j hjn).symm

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite labeled coset complexes, purity, growth, incidence bounds, and weighted expansion reduction.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.CosetConstruction

section

open CoboundaryExpanders.Complex

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem vertex_type_eq {H : Fin (n + 1) → Subgroup G} {g h : G} {i j : Fin (n + 1)}
    (heq : vertex H g i = vertex H h j) : i = j :=
  congrArg Sigma.fst ((labelEquiv H).injective heq)

theorem vertex_injective (H : Fin (n + 1) → Subgroup G) (g : G) :
    Function.Injective (vertex H g) := fun _ _ heq => vertex_type_eq heq

theorem vertex_eq_iff (H : Fin (n + 1) → Subgroup G) (g h : G) (i : Fin (n + 1)) :
    vertex H g i = vertex H h i ↔ g⁻¹ * h ∈ H i := by
  change labelEquiv H ⟨i, (g : G ⧸ H i)⟩ = labelEquiv H ⟨i, (h : G ⧸ H i)⟩ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  simpa using (QuotientGroup.eq (s := H i) (a := g) (b := h))

@[simp] theorem card_chamber (H : Fin (n + 1) → Subgroup G) (g : G) :
    (chamber H g).card = n + 1 := by
  rw [chamber, Finset.card_image_of_injective _ (vertex_injective H g)]
  simp

@[simp] theorem chamber_mem_facesOf (H : Fin (n + 1) → Subgroup G) (g : G) :
    chamber H g ∈ (complex H).facesOf n := by
  exact (mem_facesOf _ _ _).mpr ⟨mem_faces.mpr ⟨g, Finset.Subset.refl _⟩,
    card_chamber H g⟩

theorem pure (H : Fin (n + 1) → Subgroup G) : (complex H).Pure n := by
  refine ⟨⟨chamber H 1, chamber_mem_facesOf H 1⟩, ?_⟩
  intro σ hσ
  obtain ⟨g, hg⟩ := mem_faces.mp hσ
  exact ⟨chamber H g, chamber_mem_facesOf H g, hg⟩

theorem walk_of_common_chamber {H : Fin (n + 1) → Subgroup G} {g : G}
    {v w : Fin (Fintype.card (Vertex H))} (hv : v ∈ chamber H g) (hw : w ∈ chamber H g) :
    Walk H v w := by
  by_cases heq : v = w
  · subst w
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨heq,
      mem_faces.mpr ⟨g, by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hv hw⟩⟩

theorem walk_symm {H : Fin (n + 1) → Subgroup G} {v w}
    (h : Walk H v w) : Walk H w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact (Relation.ReflTransGen.single ⟨hab.1.symm,
      by simpa only [Finset.pair_comm] using hab.2⟩).trans ih

theorem walk_vertex_mul (H : Fin (n + 1) → Subgroup G)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (x : G) :
    ∀ g : G, Walk H (vertex H g 0) (vertex H (g * x) 0) := by
  have hx : x ∈ Subgroup.closure (⋃ i, (H i : Set G)) := by
    rw [hgen]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    intro g
    have hcommon : vertex H g i = vertex H (g * x) i :=
      (vertex_eq_iff H g (g * x) i).mpr (by simpa using hxi)
    have hleft := walk_of_common_chamber (vertex_mem_chamber H g 0)
      (vertex_mem_chamber H g i)
    have hright := walk_of_common_chamber (vertex_mem_chamber H (g * x) i)
      (vertex_mem_chamber H (g * x) 0)
    rw [← hcommon] at hright
    exact hleft.trans hright
  | one =>
    intro g
    simpa only [mul_one] using
      (Relation.ReflTransGen.refl : Walk H (vertex H g 0) (vertex H g 0))
  | mul x y hx hy ihx ihy =>
    intro g
    simpa only [mul_assoc] using (ihx g).trans (ihy (g * x))
  | inv x hx ih =>
    intro g
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using walk_symm (ih (g * x⁻¹))

theorem connected (H : Fin (n + 1) → Subgroup G)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) :
    (complex H).Connected := by
  refine ⟨⟨vertex H 1 0⟩, ?_⟩
  intro v w
  obtain ⟨i, g, rfl⟩ := vertex_surjective H v
  obtain ⟨j, h, rfl⟩ := vertex_surjective H w
  have hleft := walk_of_common_chamber (vertex_mem_chamber H g i)
    (vertex_mem_chamber H g 0)
  have hright := walk_of_common_chamber (vertex_mem_chamber H h 0)
    (vertex_mem_chamber H h j)
  have hmid := walk_vertex_mul H hgen (g⁻¹ * h) g
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at hmid
  exact hleft.trans (hmid.trans hright)

theorem card_incidentInChamber (H : Fin (n + 1) → Subgroup G) (g : G)
    (v : Fin (Fintype.card (Vertex H))) (d : ℕ) (hv : v ∈ chamber H g) :
    (incidentInChamber H g v d).card = Nat.choose n d := by
  have h := Finset.card_filter_powersetCard_subset {v} (chamber H g) (d + 1)
    (Finset.singleton_subset_iff.mpr hv) (by simp)
  simpa [incidentInChamber] using h

attribute [local instance] OAI.CoboundaryExpanders.CosetConstruction.subgroupFintype
theorem incident_faces_subset (H : Fin (n + 1) → Subgroup G) (g : G)
    (i : Fin (n + 1)) (d : ℕ) :
    ((complex H).facesOf d).filter (vertex H g i ∈ ·) ⊆
      Finset.univ.biUnion (fun h : H i =>
        incidentInChamber H (g * h) (vertex H g i) d) := by
  intro σ hσ
  obtain ⟨hσ, hv⟩ := Finset.mem_filter.mp hσ
  obtain ⟨hface, hcard⟩ := (mem_facesOf _ _ _).mp hσ
  obtain ⟨k, hk⟩ := mem_faces.mp hface
  obtain ⟨j, hj⟩ := mem_chamber.mp (hk hv)
  have hji : j = i := vertex_type_eq hj
  subst j
  have hmem : g⁻¹ * k ∈ H i := (vertex_eq_iff H g k i).mp hj.symm
  refine Finset.mem_biUnion.mpr ⟨⟨g⁻¹ * k, hmem⟩, Finset.mem_univ _, ?_⟩
  apply mem_incidentInChamber.mpr
  simpa only [mul_inv_cancel_left] using And.intro hk (And.intro hcard hv)

theorem topDegree_le (H : Fin (n + 1) → Subgroup G) (g : G)
    (i : Fin (n + 1)) (d : ℕ) :
    (complex H).topDegree d (vertex H g i) ≤ Nat.card (H i) * Nat.choose n d := by
  calc
    _ ≤ (Finset.univ.biUnion (fun h : H i =>
        incidentInChamber H (g * h) (vertex H g i) d)).card :=
      Finset.card_le_card (incident_faces_subset H g i d)
    _ ≤ ∑ h : H i, (incidentInChamber H (g * h) (vertex H g i) d).card :=
      Finset.card_biUnion_le
    _ = Nat.card (H i) * Nat.choose n d := by
      have hc (h : H i) : vertex H g i ∈ chamber H (g * h) := by
        rw [(vertex_eq_iff H g (g * h) i).mpr (by simp)]
        exact vertex_mem_chamber _ _ _
      simp_rw [card_incidentInChamber H _ _ d (hc _)]
      simp [Nat.card_eq_fintype_card]

theorem vertexCount_eq_sum_index (H : Fin (n + 1) → Subgroup G) :
    (complex H).vertexCount = ∑ i, (H i).index := by
  change Fintype.card (Vertex H) = _
  rw [← Nat.card_eq_fintype_card, Nat.card_sigma]
  simp only [Subgroup.index_eq_card]

end

variable {G : Type} [Group G] [Fintype G] {n : ℕ}

theorem vertexCount_mul_lower (H : Fin (n + 1) → Subgroup G) (M : ℕ)
    (hM : ∀ i, Nat.card (H i) ≤ M) :
    (n + 1) * Nat.card G ≤ (complex H).vertexCount * M := by
  rw [vertexCount_eq_sum_index, Finset.sum_mul]
  calc
    _ = ∑ i : Fin (n + 1), (H i).index * Nat.card (H i) := by
      simp only [mul_comm (H _).index, Subgroup.card_mul_index]
      simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hM i))

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.Construction

section
open Filter CosetConstruction _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

theorem localBound_pos : 0 < localBound p n := Nat.card_pos

theorem finiteCosetComplex_pure (hn : 1 ≤ n) (m : ℕ) :
    (finiteCosetComplex p n hn m).Pure n := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  exact CosetConstruction.pure _

theorem finiteSkeleton_pure (hn : 1 ≤ n) {d : ℕ} (hd : d ≤ n) (m : ℕ) :
    (finiteSkeleton p n hn d m).Pure d := by
  exact skeleton_pure (finiteCosetComplex_pure p n hn (m + 2)) hd

theorem finiteCosetComplex_degree (hn : 1 ≤ n) (m d : ℕ)
    (v : Fin (finiteCosetComplex p n hn m).vertexCount) :
    (finiteCosetComplex p n hn m).topDegree d v ≤ localBound p n * Nat.choose n d := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  obtain ⟨i, g, rfl⟩ := vertex_surjective (reducedLocalGroup p n hn m) v
  exact (topDegree_le _ _ _ _).trans
    (Nat.mul_le_mul_right _ (reducedLocalGroup_card_le p n hn m i))

theorem finiteSkeleton_degree (hn : 1 ≤ n) (d m : ℕ)
    (v : Fin (finiteSkeleton p n hn d m).vertexCount) :
    (finiteSkeleton p n hn d m).topDegree d v ≤ localBound p n * Nat.choose n d := by
  classical
  change ((finiteCosetComplex p n hn (m + 2)).skeleton d).topDegree d v ≤ _
  unfold Complex.topDegree
  rw [skeleton_facesOf le_rfl]
  exact finiteCosetComplex_degree p n hn (m + 2) d v

theorem finiteCosetComplex_growth_bound (hn : 1 ≤ n) (m : ℕ) :
    p ^ m ≤ (finiteCosetComplex p n hn m).vertexCount * localBound p n := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  exact (gquot_card_lower p n hn m).trans
    ((Nat.le_mul_of_pos_left _ (Nat.succ_pos n)).trans
      (vertexCount_mul_lower _ (localBound p n) (reducedLocalGroup_card_le p n hn m)))

theorem finiteSkeleton_growth (hn : 1 ≤ n) (d : ℕ) :
    Tendsto (fun m => (finiteSkeleton p n hn d m).vertexCount) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  apply eventually_atTop.mpr
  refine ⟨b * localBound p n, fun m hm => ?_⟩
  apply (Nat.mul_le_mul_right_iff (localBound_pos p n)).mp
  exact hm.trans ((Nat.le_add_right m 2).trans
    ((Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)).trans
      (finiteCosetComplex_growth_bound p n hn (m + 2))))

theorem finiteSkeleton_vertex_faces_growth (hn : 1 ≤ n) (d : ℕ) :
    Tendsto (fun m => ((finiteSkeleton p n hn d m).facesOf 0).card) atTop atTop := by
  simpa only [Complex.card_facesOf_zero] using finiteSkeleton_growth p n hn d

theorem constructed_pure_bounded_growing (d : ℕ) (hd : 3 ≤ d) :
    ∃ D : ℕ, (∀ m, (finiteSkeleton p (2 * d) (by omega) d m).Pure d) ∧
      Tendsto (fun m => ((finiteSkeleton p (2 * d) (by omega) d m).facesOf 0).card)
        atTop atTop ∧
      ∀ m (v : Fin (finiteSkeleton p (2 * d) (by omega) d m).vertexCount),
        (finiteSkeleton p (2 * d) (by omega) d m).topDegree d v ≤ D := by
  refine ⟨localBound p (2 * d) * Nat.choose (2 * d) d, ?_, ?_, ?_⟩
  · exact fun m => finiteSkeleton_pure p (2 * d) (by omega) (by omega) m
  · exact finiteSkeleton_vertex_faces_growth p (2 * d) (by omega) d
  · exact fun m v => finiteSkeleton_degree p (2 * d) (by omega) d m v

end

open Filter _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

theorem finiteCosetComplex_connected (hn : 2 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    (finiteCosetComplex p n (by omega) m).Connected := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  exact CosetConstruction.connected _ (quotient_locals_generate p n m hn hm)

theorem finiteSkeleton_connected (hn : 2 ≤ n) (d m : ℕ) (hd : 1 ≤ d) :
    (finiteSkeleton p n (by omega) d m).Connected := by
  exact skeleton_connected (finiteCosetComplex_connected p n hn (m + 2) (by omega)) hd

theorem constructed_connected_pure_bounded_growing (d : ℕ) (hd : 3 ≤ d) :
    ∃ D : ℕ,
      (∀ m, (finiteSkeleton p (2 * d) (by omega) d m).Pure d ∧
        (finiteSkeleton p (2 * d) (by omega) d m).Connected) ∧
      Tendsto (fun m => ((finiteSkeleton p (2 * d) (by omega) d m).facesOf 0).card)
        atTop atTop ∧
      ∀ m (v : Fin (finiteSkeleton p (2 * d) (by omega) d m).vertexCount),
        (finiteSkeleton p (2 * d) (by omega) d m).topDegree d v ≤ D := by
  obtain ⟨D, hpure, hgrowth, hdegree⟩ := constructed_pure_bounded_growing p d hd
  exact ⟨D, fun m => ⟨hpure m, finiteSkeleton_connected p (2 * d) (by omega) d m (by omega)⟩,
    hgrowth, hdegree⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Complex

open CategoryTheory

theorem cocycles_eq_coboundaries_of_homology_isZero (X : Complex) (i : ℕ)
    (homologyZero : Limits.IsZero (X.chainComplex.homology (i + 1))) :
    X.cocycles (i + 1) = X.coboundaries (i + 1) := by
  have he := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr homologyZero
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)] at he
  have hr := he.moduleCat_range_eq_ker
  change LinearMap.range (X.chainComplex.d (i + 2) (i + 1)).hom =
    LinearMap.ker (X.chainComplex.d (i + 1) i).hom at hr
  rw [chainComplex_d, chainComplex_d] at hr
  change LinearMap.range (X.boundaryLinear (i + 1)) = LinearMap.ker (X.boundaryLinear i) at hr
  unfold boundaryLinear at hr
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range] at hr
  have hh := Subspace.dualAnnihilator_inj.mp hr
  change LinearMap.ker (X.coboundaryLinear (i + 1)) =
    LinearMap.range (X.coboundaryLinear i) at hh
  ext f
  change (X.coboundaryLinear (i + 1) f = 0) ↔ ∃ g, X.coboundary i g = f
  exact Set.ext_iff.mp (congrArg (fun W : Submodule (ZMod 2) (X.Cochain (i + 1)) => W.carrier) hh) f

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.CosetConstruction
open CategoryTheory
variable {G : Type} [Group G] [Fintype G] {n : ℕ}
variable (H : Fin (n+1) → Subgroup G)

theorem cocycles_eq_coboundaries_of_typed_homology (i : ℕ)
    (hz : Limits.IsZero ((TypedCosetFaces.complex H).chainComplex.homology (i+1))) :
    (complex H).cocycles (i+1) = (complex H).coboundaries (i+1) := by
  apply Complex.cocycles_eq_coboundaries_of_homology_isZero
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ (i+1)).mapIso (typedChainIso H)).symm

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.Construction
open CategoryTheory _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

theorem finiteCosetComplex_positive_cohomology (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (m i : ℕ)
    (hm : 2 ≤ m) (hi : 0 < i) (hin : i < n-1)
    (hz : CongruenceCokernels.ProZero p (n-1) i)
    (hz' : CongruenceCokernels.ProZero p n i) :
    (finiteCosetComplex p n (by omega) m).cocycles i =
      (finiteCosetComplex p n (by omega) m).coboundaries i := by
  classical
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact CosetConstruction.cocycles_eq_coboundaries_of_typed_homology
    (reducedLocalGroup p n (by omega) m) j
    (quotientTyped_homology_isZero p n hn hp hL m (j+1) hm hi hin hz hz')

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Complex

theorem cofaceCount_le_topDegree {X : Complex} {i : ℕ} (σ : X.Face i)
    (n : ℕ) (v : Fin X.vertexCount) (hv : v ∈ σ.val) :
    X.cofaceCount n σ.val ≤ X.topDegree n v := by
  apply Finset.card_le_card
  intro τ hτ
  obtain ⟨hτ, hστ⟩ := Finset.mem_filter.mp hτ
  exact Finset.mem_filter.mpr ⟨hτ, hστ hv⟩

theorem cofaceCount_pos_of_pure {X : Complex} {n i : ℕ} (hX : X.Pure n)
    (σ : X.Face i) : 0 < X.cofaceCount n σ.val := by
  obtain ⟨τ,hτ,hστ⟩ := hX.2 σ.val (face_mem σ)
  exact Finset.card_pos.mpr ⟨τ,Finset.mem_filter.mpr ⟨hτ,hστ⟩⟩

theorem skeleton_cocycles {X : Complex} {s i : ℕ} (hi : i < s) :
    (X.skeletonCochainEquiv hi.le) '' X.cocycles i = (X.skeleton s).cocycles i := by
  ext f
  obtain ⟨f₀,rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective f
  simp only [Set.mem_image, Set.mem_ofPred_eq, cocycles]
  constructor
  · rintro ⟨g,hg,he⟩
    have hg₀ : g = f₀ := (X.skeletonCochainEquiv hi.le).injective he
    subst g
    rw [X.skeleton_coboundary hi, hg, map_zero]
  · intro hf
    rw [X.skeleton_coboundary hi] at hf
    exact ⟨f₀, (X.skeletonCochainEquiv hi).injective (by simpa using hf), rfl⟩

theorem skeleton_cosystolic_iff {X : Complex} {s i : ℕ} (hi : i < s) (η : ℝ) :
    (∀ f : (X.skeleton s).Cochain i,
      η * (X.skeleton s).distance s i f ((X.skeleton s).cocycles i) ≤
        (X.skeleton s).norm s (i+1) ((X.skeleton s).coboundary i f)) ↔
    (∀ f : X.Cochain i,
      η * X.distance s i f (X.cocycles i) ≤ X.norm s (i+1) (X.coboundary i f)) := by
  constructor
  · intro h f
    have hh := h (X.skeletonCochainEquiv hi.le f)
    rw [← skeleton_cocycles hi, skeleton_distance_image,
      skeleton_coboundary X hi, skeleton_norm] at hh
    exact hh
  · intro h f
    obtain ⟨f₀,rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective f
    rw [← skeleton_cocycles hi, skeleton_distance_image,
      skeleton_coboundary X hi, skeleton_norm]
    exact h f₀

theorem ambient_cosystolic_of_skeleton {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (hi : i < s) (hs : s ≤ n) {M η : ℝ}
    (_hM : 0 < M) (hη : 0 ≤ η)
    (hc : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧
      (X.cofaceCount n ρ.val : ℝ) ≤ M)
    (hquant : ∀ f : X.Cochain i,
      η * X.distance s i f (X.cocycles i) ≤ X.norm s (i+1) (X.coboundary i f))
    (f : X.Cochain i) :
    (η/M) * X.distance n i f (X.cocycles i) ≤ X.norm n (i+1) (X.coboundary i f) := by
  have hZ : (X.cocycles i).Nonempty := ⟨0, by simp [cocycles]⟩
  have hdist := (skeleton_distance_comparison hX hi.le hs zero_lt_one hc f hZ).1
  have hnorm := (skeleton_norm_comparison hX hi hs zero_lt_one hc (X.coboundary i f)).2
  simp only [div_one] at hnorm
  apply (mul_le_mul_iff_right₀ (skeletonScale_pos hX hs)).mp
  calc
    X.skeletonScale n s * ((η / M) * X.distance n i f (X.cocycles i)) =
        η * ((X.skeletonScale n s / M) * X.distance n i f (X.cocycles i)) := by ring
    _ ≤ η * X.distance s i f (X.cocycles i) := mul_le_mul_of_nonneg_left hdist hη
    _ ≤ X.norm s (i+1) (X.coboundary i f) := hquant f
    _ ≤ X.skeletonScale n s * X.norm n (i+1) (X.coboundary i f) := hnorm

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.Construction
open _root_.OAI.CoboundaryExpanders.Complex Filter
variable (p n : ℕ) [Fact p.Prime]

theorem finiteCosetComplex_coface_bounds (hn : 1 ≤ n) (m i : ℕ)
    (σ : (finiteCosetComplex p n hn m).Face i) :
    1 ≤ ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ∧
    ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ≤ localBound p n := by
  constructor
  · exact_mod_cast cofaceCount_pos_of_pure (finiteCosetComplex_pure p n hn m) σ
  · have hp : σ.val.Nonempty := Finset.card_pos.mp (by rw [face_card σ]; omega)
    obtain ⟨v,hv⟩ := hp
    have h := (cofaceCount_le_topDegree σ n v hv).trans
      (finiteCosetComplex_degree p n hn m n v)
    simpa only [Nat.choose_self, Nat.mul_one] using (show
      ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ≤
        (localBound p n * Nat.choose n n : ℕ) from by exact_mod_cast h)

theorem constructed_expansion_of_open_inputs (d : ℕ) (hd : 3 ≤ d) (hp : Odd p)
    (hL : OppositionAcyclic p (2*d) (by omega))
    (hz : ∀ i : ℕ, 0 < i → i < d →
      CongruenceCokernels.ProZero p (2*d-1) i ∧ CongruenceCokernels.ProZero p (2*d) i)
    (hq : UniformCosystolic p (2*d) (by omega)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m i, i < d →
      ∀ f : (finiteSkeleton p (2*d) (by omega) d m).Cochain i,
        ε * (finiteSkeleton p (2*d) (by omega) d m).distance d i f
            ((finiteSkeleton p (2*d) (by omega) d m).coboundaries i) ≤
          (finiteSkeleton p (2*d) (by omega) d m).norm d (i+1)
            ((finiteSkeleton p (2*d) (by omega) d m).coboundary i f) := by
  obtain ⟨η,hη,hq⟩ := hq
  have hM : 0 < (localBound p (2*d) : ℝ) := by exact_mod_cast localBound_pos p (2*d)
  refine ⟨(η / localBound p (2*d)) / localBound p (2*d), div_pos (div_pos hη hM) hM, ?_⟩
  intro m i hi f
  have hvanish : (finiteCosetComplex p (2*d) (by omega) (m+2)).cocycles i =
      (finiteCosetComplex p (2*d) (by omega) (m+2)).coboundaries i := by
    by_cases hi0 : i = 0
    · subst i
      exact cocycles_zero_eq_coboundaries_of_connected
        (finiteCosetComplex_connected p (2*d) (by omega) (m+2) (by omega))
    · exact finiteCosetComplex_positive_cohomology p (2*d) (by omega) hp hL
        (m+2) i (by omega) (by omega) (by omega) (hz i (by omega) hi).1 (hz i (by omega) hi).2
  apply skeleton_expansion (finiteCosetComplex_pure p (2*d) (by omega) (m+2)) hi (by omega)
    (div_nonneg hη.le hM.le) (finiteCosetComplex_coface_bounds p (2*d) (by omega) (m+2) d)
    hvanish _ f
  intro g
  exact ambient_cosystolic_of_skeleton
    (finiteCosetComplex_pure p (2*d) (by omega) (m+2)) (by omega : i < 2*d-1)
    (by omega) hM hη.le (finiteCosetComplex_coface_bounds p (2*d) (by omega) (m+2) (2*d-1))
    ((skeleton_cosystolic_iff (by omega : i < 2*d-1) η).mp (hq (m+2) (by omega) i (by omega))) g

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders
open Construction

theorem reduction_to_three_open_inputs
    (hinputs : ∀ d : ℕ, ∀ hd : 3 ≤ d, ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧
      letI : Fact p.Prime := ⟨hp⟩
      OppositionAcyclic p (2*d) (by omega) ∧
      (∀ i : ℕ, 0 < i → i < d →
        CongruenceCokernels.ProZero p (2*d-1) i ∧ CongruenceCokernels.ProZero p (2*d) i) ∧
      UniformCosystolic p (2*d) (by omega)) : MainStatement := by
  intro d hd
  obtain ⟨p,hp,ho,hL,hz,hq⟩ := hinputs d hd
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨D,hPC,hgrowth,hdegree⟩ := constructed_connected_pure_bounded_growing p d hd
  obtain ⟨ε,hε,hexp⟩ := constructed_expansion_of_open_inputs p d hd ho hL hz hq
  exact ⟨D,ε,hε,finiteSkeleton p (2*d) (by omega) d,hPC,hgrowth,hdegree,hexp⟩

end CoboundaryExpanders

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_ProStability
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive exactness, coefficient change, Bockstein groups, integral pro-stability support, and F2 reductions.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Construction
open Elementary
variable (p n : ℕ) [Fact p.Prime]

theorem U_constantCoeff (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hg : g ∈ U p (n+1)) (i j : Fin (n+1)) (hji : j ≤ i) :
    (g i j).constantCoeff = if i=j then 1 else 0 := by
  change IsUpperUnitriangular _ (evalZero p (n+1) g) at hg
  have h := hg i j hji
  change Polynomial.eval 0 (g i j) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)) i j at h
  change (g i j).coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa only [Matrix.one_apply] using h

theorem cycleGenerated_eq_U (hn : 2 ≤ n) :
    cycleGenerated p n (by omega) = U p (n+1) := by
  apply le_antisymm (cycleGenerated_le_U p n (by omega))
  intro g hg
  apply polynomial_iwahori_mem_of_roots (U p (n+1)) (cycleGenerated p n (by omega))
    (cycleGenerated_le_U p n (by omega)) (U_constantCoeff p n) _ g hg
  intro i j hij c hc
  by_cases hlt : i < j
  · exact upper_polynomial_mem_generated p n hn hlt c
  · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    have hzero := hc hjlt
    have hx : Polynomial.X ∣ c := Polynomial.X_dvd_iff.mpr (by simpa using hzero)
    obtain ⟨f,rfl⟩ := hx
    exact X_polynomial_mem_generated p n hn hij f

theorem infinite_locals_generate (hn : 2 ≤ n) :
    Subgroup.closure (⋃ i, (uLocalGroup p n (by omega) i : Set (U p (n+1)))) = ⊤ := by
  let K : Subgroup (U p (n+1)) :=
    Subgroup.closure (⋃ i, (uLocalGroup p n (by omega) i : Set (U p (n+1))))
  have hgen : cycleGenerated p n (by omega) ≤ K.map (U p (n+1)).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    obtain ⟨cut,hcut⟩ : ∃ cut : Fin (n+1), cut ≠ j := by
      by_cases hj : j=0
      · refine ⟨Fin.last n,?_⟩
        rw [hj]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last,Fin.val_zero] at this
        omega
      · exact ⟨0,fun h => hj h.symm⟩
    let u : U p (n+1) := ⟨cycleRoot p n (by omega) j,cycleRoot_mem_U p n (by omega) j⟩
    have hu : u ∈ uLocalGroup p n (by omega) cut :=
      Subgroup.subset_closure ⟨j,Ne.symm hcut,rfl⟩
    exact ⟨u,Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨cut,hu⟩),rfl⟩
  apply top_le_iff.mp
  intro u _
  have hu : u.val ∈ cycleGenerated p n (by omega) := by rw [cycleGenerated_eq_U p n hn]; exact u.property
  obtain ⟨v,hv,hvu⟩ := hgen hu
  have hvu' : v=u := Subtype.ext hvu
  exact hvu' ▸ hv

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma boundary_pair (g : G) (i j : I) (hij : i ≠ j) :
    (complex H).boundary 1 (Finsupp.single (pairFace H g i j hij) 1) =
      Finsupp.single (singletonFace H g i) 1 + Finsupp.single (singletonFace H g j) 1 := by
  apply (complex H).embed_injective 1
  change ((complex H).embed 1).comp ((complex H).boundary 1) _ = _
  rw [(complex H).embed_boundary]
  simp only [LinearMap.comp_apply, CoboundaryExpanders.InfiniteChains.Complex.embed_single, map_add, rawBoundary_single]
  have hv : vertex H g i ≠ vertex H g j := fun h => hij (vertex_injective H g h)
  simp [pairFace,singletonFace,hv,Finset.erase_insert_of_ne,add_comm]

lemma component_same_chamber (g : G) (i j : I) : component H g i = component H g j := by
  by_cases hij : i = j
  · subst j; rfl
  have hh : component H g i + component H g j = 0 := by
    rw [component,component,← map_add,← boundary_pair H g i j hij]
    exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨_,rfl⟩
  have hc : component H g j + component H g j = 0 := by
    have htwo : (1:k) + 1 = 0 := rfl
    calc
      _ = ((1:k)+1) • component H g j := by rw [add_smul,one_smul]
      _ = 0 := by rw [htwo,zero_smul]
  calc
    component H g i = (component H g i + component H g j) + component H g j := by rw [add_assoc,hc,add_zero]
    _ = component H g j := by rw [hh,zero_add]

lemma component_mul_local (g h : G) (i : I) (hh : h ∈ H i) :
    component H g i = component H (g*h) i := by
  have hv : vertex H g i = vertex H (g*h) i := by
    apply congrArg (Sigma.mk i)
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simpa using hh
  unfold component
  congr 2
  apply Subtype.ext
  exact congrArg (fun v => ({v} : Finset (Vertex H))) hv

lemma component_mul_closure (h : G)
    (hh : h ∈ Subgroup.closure (⋃ i, (H i : Set G))) :
    ∀ g i j, component H g i = component H (g*h) j := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
    intro g i j
    exact (component_same_chamber H g i a).trans
      ((component_mul_local H g x a ha).trans (component_same_chamber H (g*x) a j))
  | one =>
    intro g i j
    simpa using component_same_chamber H g i j
  | mul a _ _ _ ia ib =>
    intro g i j
    exact (ia g i i).trans (by simpa [mul_assoc] using ib (g*a) i j)
  | inv a _ ia =>
    intro g i j
    simpa [mul_assoc] using (ia (g*a⁻¹) j i).symm

lemma component_constant (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤)
    (g h : G) (i j : I) : component H g i = component H h j := by
  have := component_mul_closure H (g⁻¹*h) (by rw [hgen]; trivial) g i j
  simpa using this

lemma singletonFace_surjective : Function.Surjective (fun gi : G × I => singletonFace H gi.1 gi.2) := by
  rintro ⟨s,⟨g,A,rfl⟩,hc⟩
  have hc' : A.card = 1 := by simpa using hc
  obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc'
  exact ⟨⟨g,i⟩,Subtype.ext (by simp [singletonFace,face])⟩

theorem augmentation_exact_of_generation [Nonempty I]
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) :
    Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1) := by
  let i : I := Classical.choice ‹Nonempty I›
  let π := (LinearMap.range ((complex H).boundary 1)).mkQ
  have hπ (c : (complex H).Chains 1) :
      π c = ((complex H).sumCoefficients 1 c) • component H 1 i := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add,hc,hd,add_smul]
    | single s r =>
      obtain ⟨⟨g,j⟩,rfl⟩ := singletonFace_surjective H s
      have hs : Finsupp.single (singletonFace H g j) r = r • Finsupp.single (singletonFace H g j) 1 := by simp
      rw [hs,map_smul]
      change r • component H g j = _
      rw [component_constant H hgen g 1 j i]
      simp
  intro c
  constructor
  · intro hc
    have hz : π c = 0 := by rw [hπ,hc,zero_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (complex H).augmentation_boundary b

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
variable (p n : ℕ) [Fact p.Prime]

theorem infinite_augmentation_exact (hn : 2 ≤ n) :
    Function.Exact ((infiniteCosetComplex p n (by omega)).boundary 1)
      ((infiniteCosetComplex p n (by omega)).sumCoefficients 1) :=
  TypedCosetFaces.augmentation_exact_of_generation _ (infinite_locals_generate p n hn)

theorem oppositionAcyclic_iff_positive (hn : 2 ≤ n) :
    OppositionAcyclic p n (by omega) ↔
      ∀ j : ℕ, 0 < j → j < n-1 →
        (infiniteCosetComplex p n (by omega)).chainComplex.ExactAt j := by
  exact ⟨And.right, fun h => ⟨infinite_augmentation_exact p n hn,h⟩⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders
open Construction

theorem reduction_to_positive_open_inputs
    (hinputs : ∀ d : ℕ, ∀ hd : 3 ≤ d, ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧
      letI : Fact p.Prime := ⟨hp⟩
      (∀ j : ℕ, 0 < j → j < 2*d-1 →
        (infiniteCosetComplex p (2*d) (by omega)).chainComplex.ExactAt j) ∧
      (∀ i : ℕ, 0 < i → i < d →
        CongruenceCokernels.ProZero p (2*d-1) i ∧ CongruenceCokernels.ProZero p (2*d) i) ∧
      UniformCosystolic p (2*d) (by omega)) : MainStatement := by
  apply reduction_to_three_open_inputs
  intro d hd
  obtain ⟨p,hp,ho,hL,hz,hq⟩ := hinputs d hd
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨p,hp,ho,(oppositionAcyclic_iff_positive p (2*d) (by omega)).mpr hL,hz,hq⟩

end CoboundaryExpanders

namespace CoboundaryExpanders.ProCoefficientChange

attribute [instance] Tower.ab Tower.mod

end CoboundaryExpanders.ProCoefficientChange

namespace CoboundaryExpanders.GroupProStability
open ProCoefficientChange
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

attribute [instance] Groups.grp

end CoboundaryExpanders.GroupProStability

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform congruence homology vanishing and the complete bounded-degree coboundary-expander theorem.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders
open Construction

/-- Zero target homology makes every actual stabilization cokernel zero,
including its literal transition map. -/
theorem proZero_of_target_vanishing (p a j : ℕ)
    (hz : ∀ m : ℕ, 1 ≤ m →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a+1) m) (ZMod 2)) j)) :
    CongruenceCokernels.ProZero p a j := by
  intro m hm
  have : Subsingleton (CongruenceCokernels.H p (a+1) m j) :=
    ModuleCat.subsingleton_of_isZero (hz m hm)
  have hs : Function.Surjective (CongruenceCokernels.stabilization p a m j) :=
    fun x => ⟨0,Subsingleton.elim _ _⟩
  have : Subsingleton (CongruenceCokernels.C p a m j) :=
    (Cokernel.surjective_iff_coker_subsingleton _).mp hs
  exact ⟨m,le_refl m,Subsingleton.elim _ _⟩

/-- The manuscript's full theorem, with one positive weighted coboundary
expansion constant in ALL degrees below d and all members of the family. -/
theorem main_oai : MainStatement := by
  apply reduction_to_positive_open_inputs
  intro d hd
  obtain ⟨Q₁,hQ₁⟩ := uniform_infinite_coset_positive (2*d) (by omega)
  obtain ⟨Q₂,hQ₂⟩ := actual_uniform_cosystolic (2*d) (by omega)
  obtain ⟨Q₃,hQ₃⟩ := uniform_gamma_vanishing (2*d+1)
  obtain ⟨p,hbound,hp⟩ := Nat.exists_infinite_primes (max 3 (max Q₁ (max Q₂ Q₃))+1)
  have hQ : max 3 (max Q₁ (max Q₂ Q₃)) < p := by omega
  have hp2 : p ≠ 2 := by have := le_max_left 3 (max Q₁ (max Q₂ Q₃)); omega
  have ho : Odd p := hp.odd_of_ne_two hp2
  let : Fact p.Prime := ⟨hp⟩
  have h₁ : Q₁ < p := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hQ
  have h₂ : Q₂ < p := lt_of_le_of_lt
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hQ
  have h₃ : Q₃ < p := lt_of_le_of_lt
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hQ
  refine ⟨p,hp,ho,hQ₁ p h₁,?_,hQ₂ p inferInstance h₂⟩
  intro j hj hjd
  constructor
  · apply proZero_of_target_vanishing
    intro m hm
    exact hQ₃ p ho h₃ j hj (2*d-1+1) (by omega) (by omega) m hm
  · apply proZero_of_target_vanishing
    intro m hm
    exact hQ₃ p ho h₃ j hj (2*d+1) (by omega) (by omega) m hm

end CoboundaryExpanders

end

end OAI
end

theorem solution : type_of% @OAI.CoboundaryExpanders.main_oai := @OAI.CoboundaryExpanders.main_oai
