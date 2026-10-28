-- Prove2me | solution 1 for OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:22:18.724991+00:00
-- url     : https://prove2.me/submissions/144b5f0e-6343-4f52-9ff2-21e44bb678f5

import Mathlib
import Definitions.Def_OAIB3Kr013

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FactorIndependence
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.DetectingSpace.quotientNormedRing _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct


open scoped InnerProductSpace
namespace KirchbergRordam.GenericRW
namespace FactorIndependence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

lemma star_diagonal (T : H →L[ℂ] H) : star (diagonal (ι := ι) T) = diagonal (star T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, diagonal_apply]
  congr 1
  funext i
  exact (ContinuousLinearMap.adjoint_inner_left T (y i) (x i)).symm

lemma projection_commutes (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : ∀ x ∈ K, T x ∈ K) (hTs : ∀ x ∈ K, star T x ∈ K) :
    Commute K.starProjection T := by
  have hp (S : H →L[ℂ] H) (hS : ∀ x ∈ K, S x ∈ K) :
      K.starProjection * S * K.starProjection = S * K.starProjection := by
    ext x
    exact K.starProjection_eq_self_iff.mpr (hS _ (by simp))
  have h₁ := hp T hT
  have h₂ := congrArg star (hp (star T) hTs)
  simp only [star_mul, star_star, (isSelfAdjoint_starProjection K).star_eq] at h₂
  exact h₂.symm.trans (by rwa [mul_assoc] at h₁)

variable [DecidableEq ι]

omit [CompleteSpace H] in
lemma sum_injection (x : SumHilbert ι H) : ∑ i, injection i (x i) = x := by
  apply PiLp.ext
  intro j
  simp

omit [CompleteSpace H] [Fintype ι] in
lemma diagonal_injection (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonal T (injection (ι := ι) i x) = injection i (T x) := by
  ext j
  by_cases hj : j = i <;> simp [hj]

omit [CompleteSpace H] [Fintype ι] in
lemma entry_commutes (P : SumHilbert ι H →L[ℂ] SumHilbert ι H) (T : H →L[ℂ] H)
    (hc : Commute P (diagonal T)) (i j : ι) : Commute (entry P i j) T := by
  ext x
  have hh := congrArg (fun S : SumHilbert ι H →L[ℂ] SumHilbert ι H => S (injection j x) i) hc.eq
  simpa [mul_apply_eq_comp, diagonal_injection] using hh

omit [CompleteSpace H] in
lemma apply_eq_sum_entries (P : SumHilbert ι H →L[ℂ] SumHilbert ι H)
    (x : SumHilbert ι H) (i : ι) : P x i = ∑ j, entry P i j (x j) := by
  conv_lhs => rw [← sum_injection x]
  simp

omit [CompleteSpace H] in

lemma invariant_closure (K : Submodule ℂ H) (T : H →L[ℂ] H)
    (h : ∀ x ∈ K, T x ∈ K) : ∀ x ∈ K.topologicalClosure, T x ∈ K.topologicalClosure :=
  Set.MapsTo.closure h T.continuous

omit [DecidableEq ι] in
lemma columnSpace_closed (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H) :
    IsClosed (columnSpace M b : Set (SumHilbert ι H)) :=
  Submodule.isClosed_topologicalClosure _

omit [DecidableEq ι] in
lemma generator_mem (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H)
    (c : H →L[ℂ] H) (hc : c ∈ M.commutant) (ξ : H) :
    diagonal c (column b ξ) ∈ columnSpace M b :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨c, hc, ξ, rfl⟩)

omit [DecidableEq ι] in
lemma column_mem (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H) (ξ : H) :
    column b ξ ∈ columnSpace M b := by
  simpa only [show diagonal (ι := ι) (1 : H →L[ℂ] H) = 1 by ext; rfl,
    one_apply_eq_self] using generator_mem M b 1 (one_mem _) ξ

omit [CompleteSpace H] in
lemma invariant_span_closure (S : Set H) (T : H →L[ℂ] H)
    (h : ∀ x ∈ S, T x ∈ Submodule.span ℂ S) :
    ∀ x ∈ (Submodule.span ℂ S).topologicalClosure,
      T x ∈ (Submodule.span ℂ S).topologicalClosure := by
  apply invariant_closure
  have hh : Submodule.span ℂ S ≤ (Submodule.span ℂ S).comap T.toLinearMap :=
    Submodule.span_le.mpr h
  exact hh

omit [DecidableEq ι] in
lemma commutant_invariant (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H)
    (T : H →L[ℂ] H) (hT : T ∈ M.commutant) :
    ∀ x ∈ columnSpace M b, diagonal T x ∈ columnSpace M b := by
  apply invariant_span_closure
  rintro x ⟨c, hc, ξ, rfl⟩
  apply Submodule.subset_span
  refine ⟨T * c, mul_mem hT hc, ξ, ?_⟩
  rfl

omit [DecidableEq ι] in
lemma algebra_invariant (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H)
    (hb : ∀ i, b i ∈ M.commutant) (T : H →L[ℂ] H) (hT : T ∈ M) :
    ∀ x ∈ columnSpace M b, diagonal T x ∈ columnSpace M b := by
  apply invariant_span_closure
  rintro x ⟨c, hc, ξ, rfl⟩
  apply Submodule.subset_span
  refine ⟨c, hc, T ξ, ?_⟩
  ext i
  have h₁ := congrArg (fun S : H →L[ℂ] H => S (b i ξ))
    (VonNeumannAlgebra.mem_commutant_iff.mp hc T hT)
  have h₂ := congrArg (fun S : H →L[ℂ] H => S ξ)
    (VonNeumannAlgebra.mem_commutant_iff.mp (hb i) T hT)
  change T (c (b i ξ)) = c (b i (T ξ))
  exact h₁.trans (congrArg c h₂)


lemma columnSpace_eq_top (M : VonNeumannAlgebra H) (hM : IsFactor M)
    (b : ι → H →L[ℂ] H) (hb : ∀ i, b i ∈ M.commutant)
    (hli : LinearIndependent ℂ b) : columnSpace M b = ⊤ := by
  let K := columnSpace M b
  let : CompleteSpace K := (columnSpace_closed M b).completeSpace_coe
  let p : SumHilbert ι H →L[ℂ] SumHilbert ι H := 1 - K.starProjection
  have hp (T : H →L[ℂ] H)
      (hT : ∀ x ∈ K, diagonal T x ∈ K)
      (hTs : ∀ x ∈ K, diagonal (star T) x ∈ K) : Commute p (diagonal T) := by
    have hc := projection_commutes K (diagonal T) hT (by rwa [star_diagonal])
    change (1 - K.starProjection) * diagonal T = diagonal T * (1 - K.starProjection)
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc.eq]
  have he (i j : ι) : ∃ z : ℂ, entry p i j = z • 1 := by
    apply hM
    · rw [← M.commutant_commutant]
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro T hT
      exact (entry_commutes p T (hp T (commutant_invariant M b T hT)
        (commutant_invariant M b (star T) (star_mem hT))) i j).eq.symm
    · apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro T hT
      exact (entry_commutes p T (hp T (algebra_invariant M b hb T hT)
        (algebra_invariant M b hb (star T) (star_mem hT))) i j).eq.symm
  choose z hz using he
  have hpcol (ξ : H) : p (column b ξ) = 0 := by
    change column b ξ - K.starProjection (column b ξ) = 0
    rw [K.starProjection_eq_self_iff.mpr (column_mem M b ξ), sub_self]
  have hz0 (i : ι) : ∀ j, z i j = 0 := by
    apply (Fintype.linearIndependent_iff.mp hli) (z i)
    ext ξ
    have hh := congrArg (fun v : SumHilbert ι H => v i) (hpcol ξ)
    rw [apply_eq_sum_entries] at hh
    simpa [hz] using hh
  have hp0 : p = 0 := by
    ext x i
    rw [apply_eq_sum_entries]
    simp [hz, hz0]
  apply top_unique
  intro x _
  apply K.starProjection_eq_self_iff.mp
  have hh := congrArg (fun P : SumHilbert ι H →L[ℂ] SumHilbert ι H => P x) hp0
  change x - K.starProjection x = 0 at hh
  exact (sub_eq_zero.mp hh).symm

omit [CompleteSpace H] in
lemma row_injection (a : ι → H →L[ℂ] H) (i : ι) (x : H) :
    row a (injection i x) = a i x := by
  simp only [row_apply, injection_apply, apply_ite, map_zero]
  simp

omit [DecidableEq ι] in
theorem relation_coefficients_zero (M : VonNeumannAlgebra H) (hM : IsFactor M)
    (a b : ι → H →L[ℂ] H) (ha : ∀ i, a i ∈ M) (hb : ∀ i, b i ∈ M.commutant)
    (hli : LinearIndependent ℂ b) (hrel : ∑ i, a i * b i = 0) : ∀ i, a i = 0 := by
  classical
  have hK : columnSpace M b ≤ (row a).ker := by
    apply Submodule.topologicalClosure_minimal _ _ (row a).isClosed_ker
    apply Submodule.span_le.mpr
    rintro x ⟨c, hc, ξ, rfl⟩
    change row a (diagonal c (column b ξ)) = 0
    rw [row_apply]
    simp only [diagonal_apply, column_apply]
    calc
      ∑ i, a i (c (b i ξ)) = ∑ i, c (a i (b i ξ)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun S : H →L[ℂ] H => S (b i ξ))
          (VonNeumannAlgebra.mem_commutant_iff.mp hc (a i) (ha i))
      _ = c ((∑ i, a i * b i) ξ) := by simp
      _ = 0 := by rw [hrel]; simp
  rw [columnSpace_eq_top M hM b hb hli] at hK
  intro i
  ext ξ
  have hh := hK (show injection i ξ ∈ (⊤ : Submodule ℂ (SumHilbert ι H)) from trivial)
  change row a (injection i ξ) = 0 at hh
  rwa [row_injection] at hh

end FactorIndependence
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.GroupedFactors
open scoped Pointwise
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


lemma mem_commutantOf_iff (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ commutantOf S ↔ ∀ a ∈ S, Commute a T := by
  change T ∈ StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) ↔ _
  rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq,
    Set.union_self]
  rfl

lemma subset_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∀ a ∈ S, a ∈ bicommutant S := by
  intro a ha
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  exact ((mem_commutantOf_iff S T).mp hT a ha).eq.symm

lemma closures_commute (S T : StarSubalgebra ℂ (H →L[ℂ] H))
    (hc : ∀ a ∈ S, ∀ b ∈ T, Commute a b) :
    ∀ a ∈ bicommutant S, ∀ b ∈ bicommutant T, Commute a b := by
  intro a ha b hb
  apply VonNeumannAlgebra.mem_commutant_iff.mp hb
  apply (mem_commutantOf_iff T a).mpr
  intro t ht
  exact VonNeumannAlgebra.mem_commutant_iff.mp ha t
    ((mem_commutantOf_iff S t).mpr (fun s hs => hc s hs t ht))


theorem isFactor_of_total (S T : StarSubalgebra ℂ (H →L[ℂ] H))
    (hc : ∀ a ∈ S, ∀ b ∈ T, Commute a b)
    (htotal : ∀ U : H →L[ℂ] H,
      (∀ a ∈ S, Commute U a) → (∀ b ∈ T, Commute U b) → ∃ z : ℂ, U = z • 1) :
    FactorIndependence.IsFactor (bicommutant S) := by
  intro U hU hUc
  apply htotal U
  · intro a ha
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hUc a (subset_bicommutant S a ha)).symm
  · intro b hb
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hU b
      ((mem_commutantOf_iff S b).mpr (fun a ha => hc a ha b hb))).symm

end KirchbergRordam.GenericRW.GroupedFactors

namespace KirchbergRordam.GenericRW.MaxTensor
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

open scoped CStarAlgebra


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


theorem left_factor (π : Algebra A B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor
      (GroupedFactors.bicommutant (π.comp (includeLeft (A := A) (B := B))).range) := by
  apply GroupedFactors.isFactor_of_total _ (π.comp (includeRight (A := A) (B := B))).range
  · rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩
    exact (legs_commute x y).map π
  · intro T hL hR
    apply hs T
    exact commute_of_legs π T (fun a => hL _ ⟨a, rfl⟩) (fun b => hR _ ⟨b, rfl⟩)

end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.MaxTensor

variable {D C : Type*} [CStarAlgebra D] [CStarAlgebra C]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


lemma power_leg_factor (n : ℕ) (φ : (powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ψ : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (φ a) (ψ b))
    (hs : ∀ T : H →L[ℂ] H, (∀ a, Commute T (φ a)) →
      (∀ b, Commute T (ψ b)) → ∃ z : ℂ, T = z • 1)
    (i : Fin (n+1)) :
    FactorIndependence.IsFactor (GroupedFactors.bicommutant (φ.comp (leg D n i)).range) := by
  intro U hU hUc
  apply hs U
  · apply commute_of_power_legs n φ U
    intro j a
    by_cases hij : i = j
    · subst j
      exact (VonNeumannAlgebra.mem_commutant_iff.mp hUc _
        (GroupedFactors.subset_bicommutant _ _ ⟨a, rfl⟩)).symm
    · apply (VonNeumannAlgebra.mem_commutant_iff.mp hU _ ?_).symm
      apply (GroupedFactors.mem_commutantOf_iff _ _).mpr
      rintro b ⟨d, rfl⟩
      exact (commute_legs D n i j hij d a).map φ
  · intro b
    apply (VonNeumannAlgebra.mem_commutant_iff.mp hU _ ?_).symm
    apply (GroupedFactors.mem_commutantOf_iff _ _).mpr
    rintro a ⟨d, rfl⟩
    exact hc _ _

lemma power_leg_factors_commute (n : ℕ) (φ : (powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (i j : Fin (n+1)) (hij : i ≠ j) :
    ∀ b ∈ GroupedFactors.bicommutant (φ.comp (leg D n j)).range,
      b ∈ (GroupedFactors.bicommutant (φ.comp (leg D n i)).range).commutant := by
  intro b hb
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  exact (GroupedFactors.closures_commute _ _ (by
    rintro x ⟨c, rfl⟩ y ⟨d, rfl⟩
    exact (commute_legs D n i j hij c d).map φ) a ha b hb).eq

end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.ProductIndependence
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]


lemma selfAdjoint_complex_independent (v : ι → A) (hv : ∀ i, IsSelfAdjoint (v i))
    (hli : LinearIndependent ℝ v) : LinearIndependent ℂ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hr : ∑ i, (c i).re • v i = 0 := by
    have h := congrArg (fun x : A => (realPart x : A)) hc
    simpa only [map_sum, realPart_smul, (hv _).imaginaryPart, smul_zero, sub_zero,
      AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_smul, (hv _).coe_realPart, map_zero,
      AddSubgroup.coe_zero] using h
  have hi : ∑ i, (c i).im • v i = 0 := by
    have h := congrArg (fun x : A => (imaginaryPart x : A)) hc
    simpa only [map_sum, imaginaryPart_smul, (hv _).imaginaryPart, smul_zero, zero_add,
      AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_smul, (hv _).coe_realPart, map_zero,
      AddSubgroup.coe_zero] using h
  have hr0 := (Fintype.linearIndependent_iff.mp hli) _ hr
  have hi0 := (Fintype.linearIndependent_iff.mp hli) _ hi
  intro i
  exact Complex.ext (hr0 i) (hi0 i)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma pair_independent (M : VonNeumannAlgebra H) (hM : FactorIndependence.IsFactor M)
    (a : ι → H →L[ℂ] H) (b : κ → H →L[ℂ] H)
    (ha : ∀ i, a i ∈ M) (hb : ∀ j, b j ∈ M.commutant)
    (hia : LinearIndependent ℂ a) (hib : LinearIndependent ℂ b) :
    LinearIndependent ℂ (fun p : ι × κ => a p.1 * b p.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hrel : ∑ j, (∑ i, c (i,j) • a i) * b j = 0 := by
    rw [← hc, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_mul, smul_mul_assoc]
  have hcoeff := FactorIndependence.relation_coefficients_zero M hM
    (fun j => ∑ i, c (i,j) • a i) b
    (fun j => M.toStarSubalgebra.sum_mem fun i _ => M.toStarSubalgebra.smul_mem (ha i) _)
    hb hib hrel
  intro p
  exact (Fintype.linearIndependent_iff.mp hia _ (hcoeff p.2)) p.1

variable [Nontrivial H]


theorem many_independent (n : ℕ) (κ : Fin n → Type*) [∀ i, Fintype (κ i)]
    (M : Fin n → VonNeumannAlgebra H) (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (a : ∀ i, κ i → H →L[ℂ] H) (ha : ∀ i j, a i j ∈ M i)
    (hia : ∀ i, LinearIndependent ℂ (a i)) :
    LinearIndependent ℂ (fun p : ∀ i, κ i => (List.ofFn (fun i => a i (p i))).prod) := by
  classical
  induction n with
  | zero =>
    apply linearIndependent_unique_iff.mpr
    simp
  | succ n ih =>
    have htail := ih (fun i => κ i.succ) (fun i => M i.succ) (fun i => hM i.succ)
      (fun i j hij => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)))
      (fun i => a i.succ) (fun i => ha i.succ) (fun i => hia i.succ)
    have htailmem (p : ∀ i : Fin n, κ i.succ) :
        (List.ofFn (fun i => a i.succ (p i))).prod ∈ (M 0).commutant := by
      apply list_prod_mem
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm _ (ha _ _)
    have hp := pair_independent (M 0) (hM 0) (a 0)
      (fun p : ∀ i : Fin n, κ i.succ => (List.ofFn (fun i => a i.succ (p i))).prod)
      (ha 0) htailmem (hia 0) htail
    have h := hp.comp (Fin.consEquiv κ).symm (Fin.consEquiv κ).symm.injective
    simpa only [Function.comp_def, Fin.consEquiv_symm_apply, Fin.tail, List.ofFn_succ, List.prod_cons]
      using h

end KirchbergRordam.GenericRW.ProductIndependence

namespace KirchbergRordam.GenericRW.RealProduct
open scoped TensorProduct
open Module
variable {A : Type*} [CStarAlgebra A] {n : ℕ}
variable {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma multiply_injective [∀ i, FiniteDimensional ℝ (V i)]
    (f : ∀ i, V i →ₗ[ℝ] (H →L[ℂ] H))
    (hf : ∀ i, Function.Injective (f i)) (hsa : ∀ i v, IsSelfAdjoint (f i v))
    (M : Fin n → VonNeumannAlgebra H) (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (hmem : ∀ i v, f i v ∈ M i) : Function.Injective (multiply f) := by
  classical
  let b (i : Fin n) := Module.finBasis ℝ (V i)
  let B := Basis.piTensorProduct b
  apply LinearMap.injective_of_linearIndependent B.span_eq
  have hi (i : Fin n) : LinearIndependent ℂ (fun j => f i (b i j)) := by
    apply ProductIndependence.selfAdjoint_complex_independent _ (fun j => hsa _ _)
    exact (b i).linearIndependent.map' (f i) (LinearMap.ker_eq_bot.mpr (hf i))
  have hp := ProductIndependence.many_independent n _ M hM hc
    (fun i j => f i (b i j)) (fun i j => hmem i _) hi
  have hpR := hp.restrict_scalars' ℝ
  simpa only [Function.comp_def, B, Basis.piTensorProduct_apply, multiply_tprod] using hpR

lemma selfAdjoint_product (a : Fin n → A) (ha : ∀ i, IsSelfAdjoint (a i))
    (hc : ∀ i j, i ≠ j → Commute (a i) (a j)) :
    IsSelfAdjoint (List.ofFn a).prod := by
  induction n with
  | zero => simp [IsSelfAdjoint]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have ht := ih (fun i => a i.succ) (fun i => ha i.succ)
      (fun i j hij => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)))
    have hcomm : Commute (a 0) (List.ofFn (fun i : Fin n => a i.succ)).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm
    change star (a 0 * _) = _
    rw [star_mul, ht.star_eq, (ha 0).star_eq, hcomm.eq]

omit [Nontrivial H] in
lemma multiply_selfAdjoint
    (f : ∀ i, V i →ₗ[ℝ] (H →L[ℂ] H))
    (hsa : ∀ i v, IsSelfAdjoint (f i v))
    (hc : ∀ i j, i ≠ j → ∀ v w, Commute (f i v) (f j w))
    (x : ⨂[ℝ] i, V i) : IsSelfAdjoint (multiply f x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, multiply_tprod]
    exact (IsSelfAdjoint.all r).smul (selfAdjoint_product _ (fun i => hsa i _)
      (fun i j hij => hc i j hij _ _))
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

end KirchbergRordam.GenericRW.RealProduct
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DetectingSpaces
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PrimitiveSeparation.quotientNormedAlgebra _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace


open scoped BigOperators
open Set Module

namespace KirchbergRordam.GenericRW

section KernelCharts

variable {J K E : Type*} [Fintype J]


lemma axes_apply_pivot (e : J ↪ K) (y : J → ℝ) (j : J) :
    axes e y (e j) = y j := by
  classical
  simp [axes, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]

lemma axes_apply_off (e : J ↪ K) (y : J → ℝ) {k : K}
    (hk : k ∉ Set.range e) : axes e y k = 0 := by
  classical
  simp only [axes, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Pi.single_apply]
  split_ifs with h
  · exact (hk ⟨j, h.symm⟩).elim
  · rfl

lemma axes_neg (e : J ↪ K) (y : J → ℝ) : axes e (-y) = -axes e y := by
  classical
  simp [axes, Pi.single_neg, Finset.sum_neg_distrib]


lemma freeVector_of_vector (e : J ↪ K) (x : K → ℝ) :
    freeVector e (fun k => x k) = x - axes e (x ∘ e) := by
  classical
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    simp [freeVector, axes_apply_pivot]
  · simp [freeVector, hk, axes_apply_off e _ hk]

variable [Fintype K]

lemma mulVec_axes [DecidableEq J] (e : J ↪ K) (M : Matrix J K ℝ)
    (hM : ∀ j l, M j (e l) = if j = l then 1 else 0) (y : J → ℝ) :
    M.mulVec (axes e y) = y := by
  classical
  ext j
  simp [axes, Matrix.mulVec_sum, Matrix.mulVec_single, hM]


lemma mem_range_kernelChart [DecidableEq J] (e : J ↪ K) (M : E → Matrix J K ℝ)
    (hM : ∀ p j l, M p j (e l) = if j = l then 1 else 0)
    (p : E) (x : K → ℝ) (hx : (M p).mulVec x = 0) :
    x ∈ Set.range (kernelChart e M) := by
  refine ⟨(p, fun k => x k), ?_⟩
  simp only [kernelChart, freeVector_of_vector, Matrix.mulVec_sub,
    mulVec_axes e _ (hM p), hx, zero_sub, axes_neg]
  abel

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiff_freeVector (e : J ↪ K) :
    ContDiff ℝ 1 (freeVector e) := by
  classical
  apply contDiff_pi.mpr
  intro k
  dsimp [freeVector]
  split_ifs
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ _

lemma contDiff_axes (e : J ↪ K) : ContDiff ℝ 1 (axes e) := by
  classical
  apply contDiff_pi.mpr
  intro k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    simpa only [axes_apply_pivot] using (contDiff_apply ℝ ℝ j :
      ContDiff ℝ 1 (fun y : J → ℝ => y j))
  · simpa only [axes_apply_off e _ hk] using (contDiff_const :
      ContDiff ℝ 1 (fun _ : J → ℝ => (0 : ℝ)))

lemma contDiff_kernelChart (e : J ↪ K) (M : E → Matrix J K ℝ)
    (hM : ∀ j k, ContDiff ℝ 1 (fun p => M p j k)) :
    ContDiff ℝ 1 (kernelChart e M) := by
  classical
  unfold kernelChart
  refine ((contDiff_freeVector e).comp contDiff_snd).sub ?_
  apply (contDiff_axes e).comp
  apply contDiff_pi.mpr
  intro j
  apply ContDiff.sum
  intro k _
  exact ((hM j k).comp contDiff_fst).mul
    ((contDiff_pi.mp (contDiff_freeVector e) k).comp contDiff_snd)

lemma card_freeCoordinates (e : J ↪ K) :
    Fintype.card (FreeCoordinates e) = Fintype.card K - Fintype.card J := by
  classical
  simp only [FreeCoordinates, Fintype.card_subtype_compl]
  rw [Fintype.card_range e]

variable [FiniteDimensional ℝ E]


theorem exists_avoiding_kernels {B : Type*} [Countable B]
    (e : B → J ↪ K) (M : B → E → Matrix J K ℝ) [DecidableEq J]
    (hpivot : ∀ b p j l, M b p j (e b l) = if j = l then 1 else 0)
    (hsmooth : ∀ b j k, ContDiff ℝ 1 (fun p => M b p j k))
    (hdim : finrank ℝ E < Fintype.card J) :
    ∃ x : K → ℝ, ∀ b p, (M b p).mulVec x ≠ 0 := by
  classical
  cases isEmpty_or_nonempty B with
  | inl h => exact ⟨0, fun b => isEmptyElim b⟩
  | inr h =>
    have hJK : Fintype.card J ≤ Fintype.card K :=
      Fintype.card_le_of_embedding (e (Classical.choice h))
    have hD : finrank ℝ E + (Fintype.card K - Fintype.card J) < Fintype.card K :=
      by omega
    let S : Set (K → ℝ) := ⋃ b, Set.range (kernelChart (e b) (M b))
    have hbound : dimH S ≤ (finrank ℝ E + (Fintype.card K - Fintype.card J) : ℕ) := by
      change dimH (⋃ b, Set.range (kernelChart (e b) (M b))) ≤ _
      rw [dimH_iUnion]
      apply iSup_le
      intro b
      simpa only [Module.finrank_prod, Module.finrank_pi, card_freeCoordinates] using
        ((contDiff_kernelChart (e b) (M b) (hsmooth b)).of_le (by norm_num)).dimH_range_le
    have hsmall : dimH S < finrank ℝ (K → ℝ) := by
      apply hbound.trans_lt
      rw [Module.finrank_pi]
      exact_mod_cast hD
    obtain ⟨x, hx⟩ := (dense_compl_of_dimH_lt_finrank hsmall).nonempty
    refine ⟨x, fun b p hp => hx ?_⟩
    exact Set.mem_iUnion.mpr ⟨b, mem_range_kernelChart (e b) (M b) (hpivot b) p x hp⟩

end KernelCharts

section TensorMatrices

open scoped Classical

variable {N M R : Type*} [Fintype N]


lemma normalizedRow_pivot (s : Fin 2 ↪ M) (p : Fin 2 × M → ℝ) (j k : Fin 2) :
    normalizedRow s p j (s k) = if j = k then 1 else 0 := by
  simp [normalizedRow, s.injective.eq_iff, eq_comm]


lemma weightedTensorMatrix_pivot (s : N → Fin 2 ↪ M) (a : R)
    (p : (N × (Fin 2 × M) → ℝ) × (R → ℝ)) (j k : N → Fin 2) :
    weightedTensorMatrix s a p j (tensorPivot s a k) = if j = k then 1 else 0 := by
  change (if a = a then 1 else p.2 a) *
    (∏ l, normalizedRow (s l) (fun ji => p.1 (l, ji)) (j l) (s l (k l))) = _
  simp only [ite_true, one_mul, normalizedRow_pivot]
  by_cases h : j = k
  · subst k
    simp
  · rw [ite_eq_right h]
    obtain ⟨l, hl⟩ : ∃ l, j l ≠ k l := by
      by_contra! hh
      exact h (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ l) (ite_eq_right hl)

variable [Fintype M] [Fintype R]

lemma contDiff_weightedTensorMatrix (s : N → Fin 2 ↪ M) (a : R)
    (j : N → Fin 2) (k : R × (N → M)) :
    ContDiff ℝ 1 (fun p => weightedTensorMatrix s a p j k) := by
  unfold weightedTensorMatrix
  apply ContDiff.mul
  · split_ifs
    · exact contDiff_const
    · exact (contDiff_apply ℝ ℝ k.1).comp contDiff_snd
  · apply contDiff_prod
    intro l _
    unfold normalizedRow
    split_ifs
    · exact contDiff_const
    · exact contDiff_const
    · exact (contDiff_apply ℝ ℝ (l, (j l, k.2 l))).comp contDiff_fst


theorem exists_tensor_coordinates
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R × (N → M) → ℝ, ∀ (s : N → Fin 2 ↪ M) (a : R) p,
      (weightedTensorMatrix s a p).mulVec x ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_avoiding_kernels
    (fun b : (N → Fin 2 ↪ M) × R => tensorPivot b.1 b.2)
    (fun b => weightedTensorMatrix b.1 b.2)
    (fun b => weightedTensorMatrix_pivot b.1 b.2)
    (fun b => contDiff_weightedTensorMatrix b.1 b.2) (by
      simpa only [Module.finrank_prod, Module.finrank_pi, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fun] using hdim)
  exact ⟨x, fun s a p => hx (s, a) p⟩

omit [Fintype M] in
lemma normalizedRow_eq (s : Fin 2 ↪ M) (P : Matrix (Fin 2) M ℝ)
    (hP : ∀ j k, P j (s k) = if j = k then 1 else 0) :
    normalizedRow s (fun ji => P ji.1 ji.2) = P := by
  ext j i
  by_cases hi : i ∈ Set.range s
  · obtain ⟨k, rfl⟩ := hi
    exact (normalizedRow_pivot s _ j k).trans (hP j k).symm
  · have hij : i ≠ s j := fun h => hi ⟨j, h.symm⟩
    simp [normalizedRow, hi, hij]


lemma weightedTensorMatrix_mulVec (s : N → Fin 2 ↪ M) (a : R)
    (P : N → Matrix (Fin 2) M ℝ)
    (hP : ∀ l j k, P l j (s l k) = if j = k then 1 else 0)
    (u : R → ℝ) (hu : u a = 1) (x : R × (N → M) → ℝ) :
    (weightedTensorMatrix s a ((fun p => P p.1 p.2.1 p.2.2), u)).mulVec x =
      ∑ b, u b • (tensorMatrix P).mulVec (fun i => x (b, i)) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, weightedTensorMatrix,
    Fintype.sum_prod_type, normalizedRow_eq _ _ (hP _), tensorMatrix,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hc : (if b = a then 1 else u b) = u b := by split_ifs with h <;> simp_all
  simp only [hc, mul_assoc]


theorem exists_independent_tensor_coordinates
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R → (N → M) → ℝ, ∀ (s : N → Fin 2 ↪ M)
      (P : N → Matrix (Fin 2) M ℝ),
      (∀ l j k, P l j (s l k) = if j = k then 1 else 0) →
      LinearIndependent ℝ (fun a => (tensorMatrix P).mulVec (x a)) := by
  obtain ⟨x, hx⟩ := exists_tensor_coordinates (N := N) (M := M) (R := R) hdim
  refine ⟨fun a i => x (a, i), fun s P hP => ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  by_contra ha
  let u : R → ℝ := fun b => (g a)⁻¹ * g b
  have hu : u a = 1 := inv_mul_cancel₀ ha
  apply hx s a ((fun p => P p.1 p.2.1 p.2.2), u)
  rw [weightedTensorMatrix_mulVec s a P hP u hu x]
  calc
    ∑ b, u b • (tensorMatrix P).mulVec (fun i => x (b, i)) =
        (g a)⁻¹ • ∑ b, g b • (tensorMatrix P).mulVec (fun i => x (b, i)) := by
      simp only [Finset.smul_sum, smul_smul, u]
    _ = 0 := by rw [hg, smul_zero]

end TensorMatrices


lemma exists_tensor_exponent (m r : ℕ) : ∃ n ≥ 1, n * (2 * m) + r < 2 ^ n := by
  refine ⟨2 * (2 * m + r + 1), by omega, ?_⟩
  have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul (2 * m + r + 1)
  nlinarith


section TensorCoordinates

open scoped Classical
open PiTensorProduct
open scoped TensorProduct

variable {N M R : Type*} [Fintype N] [Fintype M] [Fintype R]


lemma tensorBasis_map_coordinates
    (P : N → (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (x : ⨂[ℝ] _ : N, (M → ℝ)) :
    (tensorBasis N (Fin 2)).equivFun (PiTensorProduct.map P x) =
      (tensorMatrix (fun l j i => P l (Pi.single i 1) j)).mulVec
        ((tensorBasis N M).equivFun x) := by
  classical
  conv_lhs => rw [← (tensorBasis N M).sum_equivFun x]
  ext j
  simp only [map_sum, map_smul, tensorBasis, Basis.piTensorProduct_apply,
    Pi.basisFun_apply, PiTensorProduct.map_tprod, Basis.equivFun_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Basis.piTensorProduct_repr_tprod_apply, Pi.basisFun_repr,
    Matrix.mulVec, dotProduct, tensorMatrix]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _


theorem exists_labels_normalized
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R → (⨂[ℝ] _ : N, (M → ℝ)),
      ∀ (s : N → Fin 2 ↪ M) (P : N → (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)),
      (∀ l j k, P l (Pi.single (s l k) 1) j = if j = k then 1 else 0) →
      LinearIndependent ℝ (fun a => PiTensorProduct.map P (x a)) := by
  obtain ⟨x, hx⟩ := exists_independent_tensor_coordinates (N := N) (M := M) (R := R) hdim
  refine ⟨fun a => (tensorBasis N M).equivFun.symm (x a), fun s P hP => ?_⟩
  apply LinearIndependent.of_comp (tensorBasis N (Fin 2)).equivFun.toLinearMap
  have h := hx s (fun l j i => P l (Pi.single i 1) j) hP
  simpa only [LinearEquiv.coe_coe, Function.comp_def, tensorBasis_map_coordinates,
    LinearEquiv.apply_symm_apply] using h


theorem normalize_surjection (P : (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (hP : Function.Surjective P) :
    ∃ (s : Fin 2 ↪ M) (L : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)),
      ∀ j k, L (P (Pi.single (s k) 1)) j = if j = k then 1 else 0 := by
  have hspan : Submodule.span ℝ (Set.range (fun i => P (Pi.single i 1))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hP y
    rw [← (Pi.basisFun ℝ M).sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨κ, a, ha, hsp, hli⟩ :=
    exists_linearIndependent' ℝ (fun i => P (Pi.single i 1))
  let : Fintype κ := Fintype.ofInjective a ha
  let b : Basis κ ℝ (Fin 2 → ℝ) := Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card (Fin 2) = Fintype.card κ := by
    rw [← Module.finrank_pi ℝ, Module.finrank_eq_card_basis b]
  let e : Fin 2 ≃ κ := Fintype.equivOfCardEq hcard
  let d : Basis (Fin 2) ℝ (Fin 2 → ℝ) := b.reindex e.symm
  let s : Fin 2 ↪ M := ⟨a ∘ e, ha.comp e.injective⟩
  refine ⟨s, d.equivFun, ?_⟩
  intro j k
  have hcol : P (Pi.single (s k) 1) = d k := by
    simp [d, s, b]
  rw [hcol, Basis.equivFun_self]
  simp only [eq_comm]


theorem exists_labels_surjective
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R → (⨂[ℝ] _ : N, (M → ℝ)),
      ∀ (P : N → (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)),
      (∀ l, Function.Surjective (P l)) →
      LinearIndependent ℝ (fun a => PiTensorProduct.map P (x a)) := by
  obtain ⟨x, hx⟩ := exists_labels_normalized (N := N) (M := M) (R := R) hdim
  refine ⟨x, fun P hP => ?_⟩
  choose s L hL using fun l => normalize_surjection (P l) (hP l)
  apply LinearIndependent.of_comp (PiTensorProduct.map (fun l => (L l).toLinearMap))
  have h := hx s (fun l => (L l).toLinearMap.comp (P l)) hL
  simpa only [PiTensorProduct.map_comp, LinearMap.coe_comp, Function.comp_def] using h

end TensorCoordinates

section RankReduction

open scoped Classical

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]


theorem exists_plane_quotient (hV : 2 ≤ finrank ℝ V) :
    ∃ Q : V →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective Q := by
  let b := Module.finBasis ℝ V
  let s : Fin 2 ↪ Fin (finrank ℝ V) :=
    ⟨Fin.castLE hV, Fin.castLE_injective hV⟩
  let Q : V →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.pi (fun j => b.coord (s j))
  refine ⟨Q, fun y => ⟨b.equivFun.symm (axes s y), ?_⟩⟩
  ext j
  change b.repr (b.equivFun.symm (axes s y)) (s j) = y j
  change b.equivFun (b.equivFun.symm (axes s y)) (s j) = y j
  rw [LinearEquiv.apply_symm_apply, axes_apply_pivot]


theorem exists_surjective_postcomposition (P : V →ₗ[ℝ] W)
    (hP : 2 ≤ finrank ℝ (LinearMap.range P)) :
    ∃ Q : W →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective (Q.comp P) := by
  obtain ⟨q, hq⟩ := exists_plane_quotient (V := LinearMap.range P) hP
  obtain ⟨Q, hQ⟩ := q.exists_extend
  refine ⟨Q, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hq y
  obtain ⟨v, hv⟩ := z.property
  refine ⟨v, ?_⟩
  change Q (P v) = y
  rw [hv]
  change (Q.comp (LinearMap.range P).subtype) z = y
  rw [hQ, hz]

end RankReduction


open scoped TensorProduct

universe u v

theorem tensor_real_labels
    (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hV : 2 ≤ Module.finrank ℝ V) (r : ℕ) (hr : 1 ≤ r) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ x : Fin r → (⨂[ℝ] _ : Fin n, V),
      ∀ (E : Fin n → Type v) [∀ j, AddCommGroup (E j)] [∀ j, Module ℝ (E j)]
        (P : ∀ j, V →ₗ[ℝ] E j),
        (∀ j, 2 ≤ Module.finrank ℝ (LinearMap.range (P j))) →
        LinearIndependent ℝ (fun a => PiTensorProduct.map P (x a)) := by
  classical
  obtain ⟨n, hn, hdim⟩ := exists_tensor_exponent (Module.finrank ℝ V - 2 + 2) (r - 1 + 1)
  rw [Nat.sub_add_cancel hV, Nat.sub_add_cancel hr] at hdim
  obtain ⟨c, hc⟩ := exists_labels_surjective
    (N := Fin n) (M := Fin (Module.finrank ℝ V)) (R := Fin r)
    (by simpa only [Fintype.card_fin] using hdim)
  let e := (Module.finBasis ℝ V).equivFun
  refine ⟨n, hn, (fun a => PiTensorProduct.map
    (fun _ : Fin n => e.symm.toLinearMap) (c a)), ?_⟩
  intro E hAdd hModule P hP
  choose Q hQ using fun j => exists_surjective_postcomposition (P j) (hP j)
  apply LinearIndependent.of_comp (PiTensorProduct.map Q)
  have hsurj : ∀ j, Function.Surjective
      ((Q j).comp ((P j).comp e.symm.toLinearMap)) := by
    intro j
    exact (hQ j).comp e.symm.surjective
  have h := hc (fun j => (Q j).comp ((P j).comp e.symm.toLinearMap)) hsurj
  simpa only [PiTensorProduct.map_comp, LinearMap.coe_comp, Function.comp_def] using h


end KirchbergRordam.GenericRW

universe uQuot


open Topology
namespace KirchbergRordam.GenericRW
namespace DetectingSpace


variable {D : Type*} [CStarAlgebra D]


lemma closedCommutatorIdeal_eq_top (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    closedCommutatorIdeal (D := D) = ⊤ := by
  by_contra h
  have : Nontrivial (CommutativeQuotient D) := Ideal.Quotient.nontrivial_iff.mpr h
  obtain ⟨χ, _⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero
    (not_isUnit_zero : ¬ IsUnit (0 : CommutativeQuotient D))
  let f : D →ₐ[ℂ] ℂ := (WeakDual.CharacterSpace.equivAlgHom χ).comp
    (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)))
  let : StarHomClass (D →ₐ[ℂ] ℂ) D ℂ := AlgHomClass.instStarHomClass
  exact hD.false ({toAlgHom := f, map_star' := map_star f} : D →⋆ₐ[ℂ] ℂ)


lemma commutatorIdeal_eq_top (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    commutatorIdeal (D := D) = ⊤ := by
  have h1 : (1 : D) ∈ closure (commutatorIdeal (D := D) : Set D) := by
    change (1 : D) ∈ closedCommutatorIdeal
    rw [closedCommutatorIdeal_eq_top hD]
    trivial
  obtain ⟨x, hx, hnear⟩ := Metric.mem_closure_iff.mp h1 1 zero_lt_one
  have hu : IsUnit x := by
    have hnorm : ‖1 - x‖ < 1 := by simpa only [dist_eq_norm] using hnear
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm
  have ht := (commutatorIdeal (D := D)).asIdeal.eq_top_of_isUnit_mem hx hu
  apply le_antisymm le_top
  intro x _
  change x ∈ (commutatorIdeal (D := D)).asIdeal
  rw [ht]
  trivial


lemma finiteCommutators_mono {s t : Finset (selfAdjoint D)} (h : s ⊆ t) :
    finiteCommutators s ⊆ finiteCommutators t := by
  rintro z ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, h ha, b, h hb, rfl⟩

lemma mem_commutatorIdeal_finite {x : D} (hx : x ∈ commutatorIdeal) :
    ∃ s : Finset (selfAdjoint D), x ∈ TwoSidedIdeal.span (finiteCommutators s) := by
  classical
  induction hx using TwoSidedIdeal.span_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl⟩ := hz
    exact ⟨{a, b}, TwoSidedIdeal.subset_span ⟨a, by simp, b, by simp, rfl⟩⟩
  | zero => exact ⟨∅, TwoSidedIdeal.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    refine ⟨s ∪ t, TwoSidedIdeal.add_mem _ ?_ ?_⟩
    · exact TwoSidedIdeal.span_mono (finiteCommutators_mono Finset.subset_union_left) hs
    · exact TwoSidedIdeal.span_mono (finiteCommutators_mono Finset.subset_union_right) ht
  | neg x hx ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s, TwoSidedIdeal.neg_mem _ hs⟩
  | left_absorb a x hx ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s, TwoSidedIdeal.mul_mem_left _ _ _ hs⟩
  | right_absorb b x hx ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s, TwoSidedIdeal.mul_mem_right _ _ _ hs⟩

lemma finite_commutators_span_one (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ s : Finset (selfAdjoint D), (1 : D) ∈ TwoSidedIdeal.span (finiteCommutators s) :=
  mem_commutatorIdeal_finite (by rw [commutatorIdeal_eq_top hD]; trivial)

end DetectingSpace


theorem finite_detecting_space {D : Type*} [CStarAlgebra D] [Nontrivial D]
    (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ V : Submodule ℝ D, Module.Finite ℝ V ∧
      V ≤ selfAdjoint.submodule ℝ D ∧
      ∀ (B : Type*) [CStarAlgebra B] [Nontrivial B] (φ : D →⋆ₐ[ℂ] B),
        ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y) := by
  classical
  obtain ⟨s, hs⟩ := DetectingSpace.finite_commutators_span_one hD
  let V : Submodule ℝ D := Submodule.span ℝ (Subtype.val '' (s : Set (selfAdjoint D)))
  have hmem (a : selfAdjoint D) (ha : a ∈ s) : (a : D) ∈ V :=
    Submodule.subset_span ⟨a, ha, rfl⟩
  refine ⟨V, FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image Subtype.val), ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨a, _, rfl⟩
    exact a.property
  · intro B _ _ φ
    by_contra h
    push Not at h
    have hk : TwoSidedIdeal.span (DetectingSpace.finiteCommutators s) ≤
        TwoSidedIdeal.ker φ.toRingHom := by
      apply TwoSidedIdeal.span_le.mpr
      rintro z ⟨a, ha, b, hb, rfl⟩
      apply (TwoSidedIdeal.mem_ker _).mpr
      change φ ((a : D) * b - b * a) = 0
      rw [map_sub, map_mul, map_mul, sub_eq_zero]
      exact h (a : D) (hmem a ha) (b : D) (hmem b hb)
    have h1 := hk hs
    have h1 := (TwoSidedIdeal.mem_ker _).mp h1
    change φ 1 = 0 at h1
    exact one_ne_zero (map_one φ ▸ h1)

end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_RepresentedLabels
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


namespace KirchbergRordam.GenericRW.RepresentedLabels
open Module
open scoped TensorProduct
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]

omit [Nontrivial D] in
lemma rank_two_of_detecting (V : Submodule ℝ D) [FiniteDimensional ℝ V]
    {B : Type*} [CStarAlgebra B] (φ : D →⋆ₐ[ℂ] B)
    (hd : ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y)) :
    2 ≤ finrank ℝ ((φ.toLinearMap.restrictScalars ℝ).comp V.subtype).range := by
  let f := (φ.toLinearMap.restrictScalars ℝ).comp V.subtype
  by_contra h
  change ¬ 2 ≤ finrank ℝ f.range at h
  have h1 : finrank ℝ f.range ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h1
  obtain ⟨x, hx, y, hy, hxy⟩ := hd
  obtain ⟨a, ha⟩ := hv (f.rangeRestrict ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := hv (f.rangeRestrict ⟨y, hy⟩)
  have ha' : a • (v : B) = φ x := congrArg Subtype.val ha
  have hb' : b • (v : B) = φ y := congrArg Subtype.val hb
  apply hxy
  rw [← ha', ← hb']
  show (a • (v : B)) * (b • (v : B)) = (b • (v : B)) * (a • (v : B))
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm a b]

lemma multiply_map {n : ℕ} {E F : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module ℝ (F i)]
    {A : Type*} [CStarAlgebra A]
    (f : ∀ i, F i →ₗ[ℝ] A) (g : ∀ i, E i →ₗ[ℝ] F i) (x : ⨂[ℝ] i, E i) :
    RealProduct.multiply f (PiTensorProduct.map g x) =
      RealProduct.multiply (fun i => (f i).comp (g i)) x := by
  have hh : (RealProduct.multiply f).comp (PiTensorProduct.map g) =
      RealProduct.multiply (fun i => (f i).comp (g i)) := by
    apply PiTensorProduct.ext
    ext v
    simp
  exact DFunLike.congr_fun hh x

lemma labels_map_independent {n r : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (q : (⨂[ℝ] i, V i) →ₗ[ℝ] (H →L[ℂ] H))
    (hq : Function.Injective q) (y : Fin r → ⨂[ℝ] i, V i)
    (hy : LinearIndependent ℝ y) : LinearIndependent ℝ (fun i => q (y i)) := by
  exact hy.map' q (LinearMap.ker_eq_bot.mpr hq)

lemma range_multiply_injective {n : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : Fin n → V →ₗ[ℝ] (H →L[ℂ] H))
    (hsa : ∀ i a, IsSelfAdjoint (f i a))
    (M : Fin n → VonNeumannAlgebra H)
    (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (hmem : ∀ i a, f i a ∈ M i)
 :
    Function.Injective (RealProduct.multiply (fun i => (f i).range.subtype)) := by
  exact RealProduct.multiply_injective (fun i => (f i).range.subtype)
    (fun i => Subtype.val_injective)
    (fun i v => by
      obtain ⟨a, ha⟩ := v.property
      change IsSelfAdjoint (v : H →L[ℂ] H)
      rw [← ha]
      exact hsa i a)
    M hM hc (fun i v => by
      obtain ⟨a, ha⟩ := v.property
      change (v : H →L[ℂ] H) ∈ M i
      rw [← ha]
      exact hmem i a)

lemma independent_multiply_range {n r : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : Fin n → V →ₗ[ℝ] (H →L[ℂ] H))
    (hsa : ∀ i a, IsSelfAdjoint (f i a))
    (M : Fin n → VonNeumannAlgebra H)
    (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (hmem : ∀ i a, f i a ∈ M i)
    (x : Fin r → (⨂[ℝ] _ : Fin n, V))
    (hli : LinearIndependent ℝ (fun k => PiTensorProduct.map
      (fun i => (f i).rangeRestrict) (x k))) :
    LinearIndependent ℂ (fun k => RealProduct.multiply f (x k)) := by
  have hsinj := range_multiply_injective f hsa M hM hc hmem
  let q : (⨂[ℝ] i : Fin n, (f i).range) →ₗ[ℝ] (H →L[ℂ] H) :=
    RealProduct.multiply (fun i => (f i).range.subtype)
  have hreal := labels_map_independent q hsinj _ hli
  have hreal' : LinearIndependent ℝ (fun k => RealProduct.multiply f (x k)) := by
    have he (i : Fin n) : (f i).range.subtype.comp (f i).rangeRestrict = f i := rfl
    simpa only [q, multiply_map, he] using hreal
  apply ProductIndependence.selfAdjoint_complex_independent _ ?_ hreal'
  intro k
  apply RealProduct.multiply_selfAdjoint
  · exact hsa
  · intro i j hij a b
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hc i j hij _ (hmem _ _))
      _ (hmem _ _))


theorem factor_labels (V : Submodule ℝ D) [FiniteDimensional ℝ V]
    (hsa : V ≤ selfAdjoint.submodule ℝ D)
    (hd : ∀ (B : Type u) [CStarAlgebra B] [Nontrivial B] (φ : D →⋆ₐ[ℂ] B),
      ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y))
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ x : Fin r → (⨂[ℝ] _ : Fin n, V),
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H]
        (φ : Fin n → D →⋆ₐ[ℂ] (H →L[ℂ] H))
        (M : Fin n → VonNeumannAlgebra H),
        (∀ i, FactorIndependence.IsFactor (M i)) →
        (∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant) →
        (∀ i a, φ i a ∈ M i) →
        LinearIndependent ℂ (fun k => RealProduct.multiply
          (fun i => ((φ i).toLinearMap.restrictScalars ℝ).comp V.subtype) (x k)) := by
  have hV : 2 ≤ finrank ℝ V := by
    have h := rank_two_of_detecting V (StarAlgHom.id ℂ D) (hd D (StarAlgHom.id ℂ D))
    exact h.trans (LinearMap.finrank_range_le _)
  obtain ⟨n, hn, x, hx⟩ := tensor_real_labels V hV r hr
  refine ⟨n, hn, x, ?_⟩
  intro H _ _ _ _ φ M hM hc hmem
  let f (i : Fin n) := ((φ i).toLinearMap.restrictScalars ℝ).comp V.subtype
  let E (i : Fin n) := (f i).range
  let g (i : Fin n) : V →ₗ[ℝ] E i := (f i).rangeRestrict
  have hrank (i : Fin n) : 2 ≤ finrank ℝ (g i).range := by
    rw [show (g i).range = ⊤ from (f i).range_rangeRestrict, finrank_top]
    exact rank_two_of_detecting V _ (hd _ (φ i))
  have hind := hx (fun i => E i) g hrank
  apply independent_multiply_range f (fun i a => (hsa a.property).map (φ i)) M hM hc
    (fun i a => hmem i a) x
  exact hind



lemma multiply_selfAdjoint_general {n : ℕ} {E : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    {A : Type*} [CStarAlgebra A]
    (f : ∀ i, E i →ₗ[ℝ] A)
    (hsa : ∀ i v, IsSelfAdjoint (f i v))
    (hc : ∀ i j, i ≠ j → ∀ v w, Commute (f i v) (f j w))
    (x : ⨂[ℝ] i, E i) : IsSelfAdjoint (RealProduct.multiply f x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, RealProduct.multiply_tprod]
    exact (IsSelfAdjoint.all r).smul (RealProduct.selfAdjoint_product _ (fun i => hsa i _)
      (fun i j hij => hc i j hij _ _))
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

lemma map_multiply {n : ℕ} {E : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (f : ∀ i, E i →ₗ[ℝ] A) (x : ⨂[ℝ] i, E i) :
    φ (RealProduct.multiply f x) = RealProduct.multiply
      (fun i => (φ.toLinearMap.restrictScalars ℝ).comp (f i)) x := by
  have hh : (φ.toLinearMap.restrictScalars ℝ).comp (RealProduct.multiply f) =
      RealProduct.multiply (fun i => (φ.toLinearMap.restrictScalars ℝ).comp (f i)) := by
    apply PiTensorProduct.ext
    ext v
    simp [map_list_prod, Function.comp_def]
  exact DFunLike.congr_fun hh x


theorem power_labels (V : Submodule ℝ D) [FiniteDimensional ℝ V]
    (hsa : V ≤ selfAdjoint.submodule ℝ D)
    (hd : ∀ (B : Type u) [CStarAlgebra B] [Nontrivial B] (φ : D →⋆ₐ[ℂ] B),
      ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y))
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ n : ℕ, ∃ x : Fin r → (MaxTensor.powerPack D n),
      (∀ k, IsSelfAdjoint (x k)) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H]
        (B : Type u) [CStarAlgebra B]
        (φ : (MaxTensor.powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (ψ : B →⋆ₐ[ℂ] (H →L[ℂ] H)),
        (∀ a b, Commute (φ a) (ψ b)) →
        (∀ T : H →L[ℂ] H, (∀ a, Commute T (φ a)) →
          (∀ b, Commute T (ψ b)) → ∃ z : ℂ, T = z • 1) →
        LinearIndependent ℂ (fun k => φ (x k)) := by
  obtain ⟨n, hn, v, hv⟩ := factor_labels V hsa hd r hr
  cases n with
  | zero => omega
  | succ n =>
    let f : Fin (n+1) → V →ₗ[ℝ] (MaxTensor.powerPack D n) :=
      fun i => ((MaxTensor.leg D n i).toLinearMap.restrictScalars ℝ).comp V.subtype
    let x : Fin r → (MaxTensor.powerPack D n) := fun k => RealProduct.multiply f (v k)
    refine ⟨n, x, ?_, ?_⟩
    · intro k
      apply multiply_selfAdjoint_general
      · intro i a
        exact (hsa a.property).map (MaxTensor.leg D n i)
      · intro i j hij a b
        exact MaxTensor.commute_legs D n i j hij a b
    · intro H _ _ _ _ B _ φ ψ hc hs
      let ρ (i : Fin (n+1)) := φ.comp (MaxTensor.leg D n i)
      let M (i : Fin (n+1)) := GroupedFactors.bicommutant (ρ i).range
      have hi := hv H ρ M
        (fun i => MaxTensor.power_leg_factor n φ ψ hc hs i)
        (fun i j hij => MaxTensor.power_leg_factors_commute n φ i j hij)
        (fun i a => GroupedFactors.subset_bicommutant _ _ ⟨a, rfl⟩)
      convert hi using 1
      funext k
      exact map_multiply φ f (v k)
end KirchbergRordam.GenericRW.RepresentedLabels


namespace KirchbergRordam.GenericRW.GroupedFactors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma isFactor_of_three (S T R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hST : ∀ a ∈ S, ∀ b ∈ T, Commute a b)
    (hSR : ∀ a ∈ S, ∀ c ∈ R, Commute a c)
    (hs : ∀ U : H →L[ℂ] H, (∀ a ∈ S, Commute U a) →
      (∀ b ∈ T, Commute U b) → (∀ c ∈ R, Commute U c) → ∃ z : ℂ, U = z • 1) :
    FactorIndependence.IsFactor (bicommutant S) := by
  intro U hU hUc
  apply hs U
  · intro a ha
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hUc a (subset_bicommutant S a ha)).symm
  · intro b hb
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hU b
      ((mem_commutantOf_iff S b).mpr (fun a ha => hST a ha b hb))).symm
  · intro c hc
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hU c
      ((mem_commutantOf_iff S c).mpr (fun a ha => hSR a ha c hc))).symm
end KirchbergRordam.GenericRW.GroupedFactors

namespace KirchbergRordam.GenericRW.TripleTensor
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

variable {E : Type*} [CStarAlgebra E]
lemma commute_of_legs (π : Algebra A B C →⋆ₐ[ℂ] E) (T : E)
    (h1 : ∀ a, Commute T (π (first a)))
    (h2 : ∀ b, Commute T (π (second b)))
    (h3 : ∀ c, Commute T (π (third c))) : ∀ x, Commute T (π x) := by
  apply MaxTensor.commute_of_legs π T h1
  exact MaxTensor.commute_of_legs (π.comp includeRight) T h2 h3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma first_factor (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor (GroupedFactors.bicommutant (π.comp first).range) :=
  MaxTensor.left_factor π hs
lemma second_factor (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor (GroupedFactors.bicommutant (π.comp second).range) := by
  apply GroupedFactors.isFactor_of_three _ (π.comp first).range (π.comp third).range
  · rintro x ⟨b, rfl⟩ y ⟨a, rfl⟩
    exact ((first_second a b).map π).symm
  · rintro x ⟨b, rfl⟩ y ⟨c, rfl⟩
    exact (second_third b c).map π
  · intro T h2 h1 h3
    exact hs T (commute_of_legs π T (fun a => h1 _ ⟨a, rfl⟩)
      (fun b => h2 _ ⟨b, rfl⟩) (fun c => h3 _ ⟨c, rfl⟩))


lemma complementSecond_commute (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : B) (d : MaxTensor.Algebra A C) :
    Commute (π (second b)) (complementSecond π d) := by
  apply MaxTensor.commute_of_legs (complementSecond π) _ ?_ ?_ d
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) a
    change complementSecond π (includeLeft a) = π (first a) at he
    rw [he]
    exact ((first_second a b).map π).symm
  · intro c
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) c
    change complementSecond π (includeRight c) = π (third c) at he
    rw [he]
    exact (second_third b c).map π
lemma complementSecond_total (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1)
    (T : H →L[ℂ] H) (h2 : ∀ b, Commute T (π (second b)))
    (h13 : ∀ d, Commute T (complementSecond π d)) : ∃ z : ℂ, T = z • 1 := by
  apply hs T
  apply commute_of_legs π T ?_ h2 ?_
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) a
    change complementSecond π (includeLeft a) = π (first a) at he
    rw [← he]
    exact h13 _
  · intro c
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) c
    change complementSecond π (includeRight c) = π (third c) at he
    rw [← he]
    exact h13 _

lemma complementThird_commute (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (c : C) (d : MaxTensor.Algebra A B) :
    Commute (π (third c)) (complementThird π d) := by
  apply MaxTensor.commute_of_legs (complementThird π) _ ?_ ?_ d
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) a
    change complementThird π (includeLeft a) = π (first a) at he
    rw [he]
    exact ((first_third a c).map π).symm
  · intro b
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) b
    change complementThird π (includeRight b) = π (second b) at he
    rw [he]
    exact ((second_third b c).map π).symm
lemma complementThird_total (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1)
    (T : H →L[ℂ] H) (h3 : ∀ c, Commute T (π (third c)))
    (h12 : ∀ d, Commute T (complementThird π d)) : ∃ z : ℂ, T = z • 1 := by
  apply hs T
  apply commute_of_legs π T ?_ ?_ h3
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) a
    change complementThird π (includeLeft a) = π (first a) at he
    rw [← he]
    exact h12 _
  · intro b
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) b
    change complementThird π (includeRight b) = π (second b) at he
    rw [← he]
    exact h12 _
end KirchbergRordam.GenericRW.TripleTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_NoncommutingPair
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
noncomputable section
open Topology


namespace KirchbergRordam.GenericRW
section
variable {A : Type*} [Ring A] {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma sum_commutator (a : ι → A) (b : κ → A) (x : ι → A) (y : κ → A)
    (hxb : ∀ i j, Commute (x i) (b j)) (hya : ∀ i j, Commute (y j) (a i))
    (hxy : ∀ i j, Commute (x i) (y j)) :
    (∑ i, a i * x i) * (∑ j, b j * y j) -
      (∑ j, b j * y j) * (∑ i, a i * x i) =
      ∑ p : ι × κ, (a p.1 * b p.2 - b p.2 * a p.1) * (x p.1 * y p.2) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => b j * y j * (a i * x i)), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hxb i j).mul_mul_mul_comm, (hya i j).mul_mul_mul_comm, (hxy i j).eq,
    sub_mul]
end

section
variable {A : Type*} [CStarAlgebra A] {D : Type*} [CStarAlgebra D]
variable {V : Submodule ℝ D} {ι : Type*} [Fintype ι]
lemma commute_of_basis (b : Module.Basis ι ℝ V) (φ : D →⋆ₐ[ℂ] A)
    (h : ∀ i j, Commute (φ (b i)) (φ (b j))) :
    ∀ x ∈ V, ∀ y ∈ V, Commute (φ x) (φ y) := by
  classical
  intro x hx y hy
  let x' : V := ⟨x, hx⟩
  let y' : V := ⟨y, hy⟩
  have he (z : V) : φ z = ∑ i, (b.repr z i) • φ (b i) := by
    let g := (φ.toLinearMap.restrictScalars ℝ).comp V.subtype
    have hz := congrArg g (b.sum_repr z)
    simp only [map_sum, map_smul] at hz
    exact hz.symm
  rw [show φ x = _ from he x', show φ y = _ from he y']
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((h i j).smul_left _).smul_right _
end
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.NoncommutingPair
noncomputable section
open scoped BigOperators
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]

lemma mem_factor_commutant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hc : ∀ a ∈ S, Commute a T) : T ∈ (GroupedFactors.bicommutant S).commutant := by
  rw [GroupedFactors.bicommutant, VonNeumannAlgebra.commutant_commutant]
  exact (GroupedFactors.mem_commutantOf_iff S T).mpr hc

lemma selfAdjoint_sum {ι : Type*} [Fintype ι] {A : Type*} [CStarAlgebra A]
    (f : ι → A) (hf : ∀ i, IsSelfAdjoint (f i)) : IsSelfAdjoint (∑ i, f i) := by
  change star _ = _
  simp only [star_sum, (hf _).star_eq]

lemma selfAdjoint_mul_of_commute {A : Type*} [CStarAlgebra A] {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hc : Commute a b) :
    IsSelfAdjoint (a * b) := (ha.commute_iff hb).mp hc

lemma map_sum_mul {ι : Type*} [Fintype ι] {A B : Type*}
    [CStarAlgebra A] [CStarAlgebra B] (φ : A →⋆ₐ[ℂ] B) (f g : ι → A) :
    φ (∑ i, f i * g i) = ∑ i, φ (f i) * φ (g i) := by
  simp only [map_sum, map_mul]


theorem exists_pair (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ n : ℕ, ∃ s t : TripleTensor.Algebra D (MaxTensor.powerPack D n)
        (MaxTensor.powerPack D n),
      IsSelfAdjoint s ∧ IsSelfAdjoint t ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H]
        (π : TripleTensor.Algebra D (MaxTensor.powerPack D n)
          (MaxTensor.powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H)),
        (∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ z : ℂ, T = z • 1) →
        ¬ Commute (π s) (π t) := by
  classical
  obtain ⟨V, hV, hsa, hd⟩ := finite_detecting_space hD
  let := hV
  let r := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  have hr : 1 ≤ r := by
    have h := RepresentedLabels.rank_two_of_detecting V (StarAlgHom.id ℂ D)
      (hd D (StarAlgHom.id ℂ D))
    have hh := h.trans (LinearMap.finrank_range_le _)
    exact le_trans (by norm_num) hh
  obtain ⟨n, x, hxsa, hx⟩ := RepresentedLabels.power_labels V hsa hd r hr
  let P := MaxTensor.powerPack D n
  let : CStarAlgebra (TripleTensor.Algebra D P P) := inferInstance
  let a : Fin r → TripleTensor.Algebra D P P := fun i => TripleTensor.first (b i : D)
  let l : Fin r → TripleTensor.Algebra D P P := fun i => TripleTensor.second (x i)
  let q : Fin r → TripleTensor.Algebra D P P := fun i => TripleTensor.third (x i)
  let s := ∑ i, a i * l i
  let t := ∑ i, a i * q i
  refine ⟨n, s, t, ?_, ?_, ?_⟩
  · apply selfAdjoint_sum
    intro i
    have ha : IsSelfAdjoint (a i) :=
      (hsa (b i).property).map (TripleTensor.first (B := P) (C := P))
    have hl : IsSelfAdjoint (l i) :=
      (hxsa i).map (TripleTensor.second (A := D) (C := P))
    exact selfAdjoint_mul_of_commute ha hl (TripleTensor.first_second (b i : D) (x i))
  · apply selfAdjoint_sum
    intro i
    have ha : IsSelfAdjoint (a i) :=
      (hsa (b i).property).map (TripleTensor.first (B := P) (C := P))
    have hq : IsSelfAdjoint (q i) :=
      (hxsa i).map (TripleTensor.third (A := D) (B := P))
    exact selfAdjoint_mul_of_commute ha hq (TripleTensor.first_third (b i : D) (x i))
  · intro H _ _ _ _ π hs hc
    let α : D →⋆ₐ[ℂ] (H →L[ℂ] H) := π.comp TripleTensor.first
    let β : P →⋆ₐ[ℂ] (H →L[ℂ] H) := π.comp TripleTensor.second
    let γ : P →⋆ₐ[ℂ] (H →L[ℂ] H) := π.comp TripleTensor.third
    let M := GroupedFactors.bicommutant α.range
    let N := GroupedFactors.bicommutant β.range
    have hiβ := hx H (MaxTensor.Algebra D P) β (TripleTensor.complementSecond π)
      (TripleTensor.complementSecond_commute π) (TripleTensor.complementSecond_total π hs)
    have hiγ := hx H (MaxTensor.Algebra D P) γ (TripleTensor.complementThird π)
      (TripleTensor.complementThird_commute π) (TripleTensor.complementThird_total π hs)
    have hp : LinearIndependent ℂ (fun ij : Fin r × Fin r => β (x ij.1) * γ (x ij.2)) := by
      apply ProductIndependence.pair_independent N (TripleTensor.second_factor π hs)
        _ _ (fun i => GroupedFactors.subset_bicommutant _ _ ⟨x i, rfl⟩) ?_ hiβ hiγ
      intro j
      apply mem_factor_commutant
      rintro z ⟨c, rfl⟩
      exact (TripleTensor.second_third c (x j)).map π
    have hrel : ∑ ij : Fin r × Fin r,
        (α (b ij.1) * α (b ij.2) - α (b ij.2) * α (b ij.1)) *
          (β (x ij.1) * γ (x ij.2)) = 0 := by
      have he := sum_commutator (fun i => α (b i)) (fun i => α (b i))
        (fun i => β (x i)) (fun i => γ (x i))
        (fun i j => ((TripleTensor.first_second (b j : D) (x i)).map π).symm)
        (fun i j => ((TripleTensor.first_third (b i : D) (x j)).map π).symm)
        (fun i j => (TripleTensor.second_third (x i) (x j)).map π)
      rw [← he]
      have hps : π s = ∑ i, α (b i) * β (x i) := map_sum_mul π a l
      have hpt : π t = ∑ i, α (b i) * γ (x i) := map_sum_mul π a q
      rw [← hps, ← hpt]
      exact sub_eq_zero.mpr hc.eq
    have hz := FactorIndependence.relation_coefficients_zero M
      (TripleTensor.first_factor π hs)
      (fun ij : Fin r × Fin r => α (b ij.1) * α (b ij.2) - α (b ij.2) * α (b ij.1))
      (fun ij : Fin r × Fin r => β (x ij.1) * γ (x ij.2))
      (fun ij => M.toStarSubalgebra.sub_mem
        (M.toStarSubalgebra.mul_mem (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩)
          (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩))
        (M.toStarSubalgebra.mul_mem (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩)
          (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩)))
      (fun ij => mem_factor_commutant _ _ (by
        rintro z ⟨d, rfl⟩
        exact ((TripleTensor.first_second d (x ij.1)).map π).mul_right
          ((TripleTensor.first_third d (x ij.2)).map π))) hp hrel
    obtain ⟨v, hv, w, hw, hn⟩ := hd (H →L[ℂ] H) α
    exact hn (commute_of_basis b α (fun i j => sub_eq_zero.mp (hz (i,j))) v hv w hw)
end
end KirchbergRordam.GenericRW.NoncommutingPair
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_States
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


open NormedSpace
open scoped ComplexOrder


open scoped ComplexOrder
namespace KirchbergRordam.GenericRW
namespace PureStates
variable (A : Type*) [CStarAlgebra A]

lemma normStates_compact : IsCompact (normStates A) := by
  have h := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous (1 : A)) (continuous_const (y := (1 : ℂ))))
  convert h using 1
  ext φ
  simp [normStates, Metric.mem_closedBall]

variable [Nontrivial A]

lemma normStates_nonempty : (normStates A).Nonempty := by
  obtain ⟨φ, hφ, h1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  refine ⟨(StrongDual.toWeakDual φ), hφ.le, ?_⟩
  simpa using h1


theorem exists_pure : ∃ φ : A →L[ℂ] ℂ, IsPure A φ := by
  obtain ⟨φ, hφ⟩ := (normStates_compact A).extremePoints_nonempty (normStates_nonempty A)
  exact ⟨φ.toStrongDual, hφ⟩

end PureStates
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Representations
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder


open scoped InnerProductSpace
namespace KirchbergRordam.GenericRW
namespace Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


lemma positive_zero_of_square_zero (f : A →ₚ[ℂ] ℂ) (a : A)
    (hz : f (star a * a) = 0) : f a = 0 := by
  have hvec : gnsVector f a = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [gnsVector_inner] using hz
  have hinner := gnsVector_inner f 1 a
  simpa only [hvec, inner_zero_right, star_one, one_mul] using hinner.symm

end Representations

universe u

attribute [instance] IrreducibleRepresentation.normed IrreducibleRepresentation.inner
  IrreducibleRepresentation.complete IrreducibleRepresentation.nontrivial


theorem exists_irreducible_representation (A : Type u) [CStarAlgebra A] [Nontrivial A] :
    Nonempty (IrreducibleRepresentation A) := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  obtain ⟨φ, hp⟩ := PureStates.exists_pure A
  exact ⟨Representations.pureRepresentation φ hp⟩

end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Fullness
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace


namespace KirchbergRordam.GenericRW
namespace PrimitiveSeparation
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (I : Ideal A) [I.IsTwoSided] [IsClosed (I : Set A)]

lemma quotient_norm_one (hI : I ≠ ⊤) : ‖(1 : A ⧸ I)‖ = 1 := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  apply le_antisymm _ (one_le_norm_one (A ⧸ I))
  change ‖(Submodule.Quotient.mk (1 : A) : A ⧸ I)‖ ≤ 1
  simpa only [norm_one] using Submodule.Quotient.norm_mk_le I (1 : A)


omit [Nontrivial A] [I.IsTwoSided] [IsClosed (I : Set A)] in
lemma stateFace_compact : IsCompact (stateFace I) :=
  (PureStates.normStates_compact A).inter_right
    (by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun _ =>
        isClosed_eq (WeakDual.eval_continuous a) continuous_const)

lemma stateFace_nonempty (hI : I ≠ ⊤) : (stateFace I).Nonempty := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨f, hfn, hf1⟩ := exists_dual_vector ℂ (1 : A ⧸ I) (by rw [quotient_norm_one I hI]; exact one_ne_zero)
  have hf1 : f 1 = 1 := by simpa [quotient_norm_one I hI] using hf1
  let g := f.comp (quotientCLM I)
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound (by norm_num)
    intro a
    have hq : ‖quotientCLM I a‖ ≤ ‖a‖ := Submodule.Quotient.norm_mk_le I a
    change ‖f (quotientCLM I a)‖ ≤ 1 * ‖a‖
    calc
      ‖f (quotientCLM I a)‖ ≤ ‖f‖ * ‖quotientCLM I a‖ := f.le_opNorm _
      _ ≤ 1 * ‖a‖ := by rw [hfn, one_mul, one_mul]; exact hq
  refine ⟨StrongDual.toWeakDual g, ⟨hg, ?_⟩, ?_⟩
  · change f (Ideal.Quotient.mk I 1) = 1
    simpa only [map_one] using hf1
  · intro a ha
    change f (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

variable [PartialOrder A] [StarOrderedRing A]

omit [I.IsTwoSided] [IsClosed (I : Set A)] in
lemma stateFace_isFace (φ ψ χ : WeakDual ℂ A) (hφ : ∀ a ∈ I, φ a = 0)
    (hψ : ψ ∈ PureStates.normStates A) (hχ : χ ∈ PureStates.normStates A)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (he : s • ψ + t • χ = φ) :
    (∀ a ∈ I, ψ a = 0) ∧ (∀ a ∈ I, χ a = 0) := by
  have hψp (a : A) (ha : 0 ≤ a) : 0 ≤ ψ a :=
    States.eval_nonneg ψ.toStrongDual hψ.1 hψ.2 a ha
  have hχp (a : A) (ha : 0 ≤ a) : 0 ≤ χ a :=
    States.eval_nonneg χ.toStrongDual hχ.1 hχ.2 a ha
  have hz (a : A) (ha : a ∈ I) : ψ (star a * a) = 0 ∧ χ (star a * a) = 0 := by
    have hpa := hψp (star a * a) (star_mul_self_nonneg a)
    have hca := hχp (star a * a) (star_mul_self_nonneg a)
    have he' := congrArg (fun f : WeakDual ℂ A => (f (star a * a)).re) he
    have hf := hφ (star a * a) (I.mul_mem_left _ ha)
    change ((s • ψ (star a * a) + t • χ (star a * a)) : ℂ).re = (φ (star a * a)).re at he'
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at he'
    rw [hf, Complex.zero_re] at he'
    have hp0 : (ψ (star a * a)).re = 0 := by
      nlinarith [(Complex.nonneg_iff.mp hpa).1, (Complex.nonneg_iff.mp hca).1]
    have hc0 : (χ (star a * a)).re = 0 := by
      nlinarith [(Complex.nonneg_iff.mp hpa).1, (Complex.nonneg_iff.mp hca).1]
    constructor <;> apply Complex.ext
    · exact hp0
    · exact (Complex.nonneg_iff.mp hpa).2.symm
    · exact hc0
    · exact (Complex.nonneg_iff.mp hca).2.symm
  constructor
  · intro a ha
    exact Representations.positive_zero_of_square_zero
      (PositiveLinearMap.mk₀ ψ.toStrongDual.toLinearMap hψp) a (hz a ha).1
  · intro a ha
    exact Representations.positive_zero_of_square_zero
      (PositiveLinearMap.mk₀ χ.toStrongDual.toLinearMap hχp) a (hz a ha).2


theorem exists_pure_annihilating (hI : I ≠ ⊤) :
    ∃ φ : A →L[ℂ] ℂ, PureStates.IsPure A φ ∧ ∀ a ∈ I, φ a = 0 := by
  obtain ⟨φ, hφ⟩ := (stateFace_compact I).extremePoints_nonempty (stateFace_nonempty I hI)
  refine ⟨φ.toStrongDual, ⟨hφ.1.1, ?_⟩, hφ.1.2⟩
  intro ψ hψ χ hχ he
  obtain ⟨s, t, hs, ht, hst, heq⟩ := he
  obtain ⟨hψI, hχI⟩ := stateFace_isFace I φ ψ χ hφ.1.2 hψ hχ s t hs ht heq
  exact hφ.2 ⟨hψ, hψI⟩ ⟨hχ, hχI⟩ ⟨s, t, hs, ht, hst, heq⟩

omit [IsClosed (I : Set A)] in
lemma pureRepresentation_annihilates (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : ∀ a ∈ I, φ a = 0) (a : A) (ha : a ∈ I) :
    (Representations.pureRepresentation φ hp).representation a = 0 := by
  let f := Representations.stateOfPure φ hp
  have hv (b : A) : Representations.gnsVector f (a * b) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [Representations.gnsVector_inner]
    exact hφ _ (I.mul_mem_left _ (I.mul_mem_right _ ha))
  apply ContinuousLinearMap.ext
  intro x
  have hd := Representations.gns_cyclic f
  apply hd.induction_on (p := fun x => f.gnsStarAlgHom a x = 0) x
  · exact isClosed_eq ((f.gnsStarAlgHom a).continuous) continuous_const
  · intro b
    simp only [Representations.gnsVector_apply, mul_one]
    exact hv b


theorem exists_irreducible_annihilating (hI : I ≠ ⊤) :
    ∃ ρ : IrreducibleRepresentation A, ∀ a ∈ I, ρ.representation a = 0 := by
  obtain ⟨φ, hp, hφ⟩ := exists_pure_annihilating I hI
  exact ⟨Representations.pureRepresentation φ hp,
    fun a ha => pureRepresentation_annihilates I φ hp hφ a ha⟩

end PrimitiveSeparation
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.Fullness
variable {A : Type*} [CStarAlgebra A]


lemma eq_top_of_closedIdeal_eq_top (I : TwoSidedIdeal A) (hI : closedIdeal I = ⊤) : I = ⊤ := by
  have h1 : (1 : A) ∈ closure (I : Set A) := by
    change (1 : A) ∈ closedIdeal I
    rw [hI]
    trivial
  obtain ⟨x, hx, hnear⟩ := Metric.mem_closure_iff.mp h1 1 zero_lt_one
  have hu : IsUnit x := by
    have hnorm : ‖1 - x‖ < 1 := by simpa only [dist_eq_norm] using hnear
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm
  have ht := I.asIdeal.eq_top_of_isUnit_mem hx hu
  apply le_antisymm le_top
  intro x _
  change x ∈ I.asIdeal
  rw [ht]
  trivial


lemma full_iff_closed (a : A) : IsFull a ↔ closedIdeal (TwoSidedIdeal.span {a}) = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x hx
    apply subset_closure
    rw [show TwoSidedIdeal.span {a} = ⊤ from h]
    trivial
  · exact eq_top_of_closedIdeal_eq_top _

lemma full_of_survives [Nontrivial A]
    (a : A) (h : ∀ π : IrreducibleRepresentation A, π.representation a ≠ 0) : IsFull a := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  apply (full_iff_closed a).mpr
  by_contra hn
  obtain ⟨π, hπ⟩ := PrimitiveSeparation.exists_irreducible_annihilating
    (closedIdeal (TwoSidedIdeal.span {a})) hn
  exact h π (hπ a (subset_closure (TwoSidedIdeal.subset_span rfl)))

lemma full_survives {B : Type*} [CStarAlgebra B] [Nontrivial B]
    {a : A} (ha : IsFull a) (φ : A →⋆ₐ[ℂ] B) : φ a ≠ 0 := by
  intro hz
  have hk : TwoSidedIdeal.span {a} ≤ TwoSidedIdeal.ker φ.toRingHom :=
    TwoSidedIdeal.span_le.mpr (Set.singleton_subset_iff.mpr ((TwoSidedIdeal.mem_ker _).mpr hz))
  have h1 : (1 : A) ∈ TwoSidedIdeal.span {a} := by
    rw [show TwoSidedIdeal.span {a} = ⊤ from ha]
    exact TwoSidedIdeal.mem_top A
  have hz1 := (TwoSidedIdeal.mem_ker _).mp (hk h1)
  exact one_ne_zero (by simpa only [map_one] using hz1)

lemma bridges_span_one {a b : A} (ha : IsFull a) (hb : IsFull b) :
    TwoSidedIdeal.span (Set.range (fun d : A => a * d * b)) = ⊤ := by
  let J := TwoSidedIdeal.span (Set.range (fun d : A => a * d * b))
  have hmul {x : A} (hx : x ∈ TwoSidedIdeal.span {a}) : ∀ d : A, x * d * b ∈ J := by
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx => subst x; intro d; exact TwoSidedIdeal.subset_span ⟨d, rfl⟩
    | zero => intro d; simp only [zero_mul]; exact J.zero_mem
    | add x y hx hy ihx ihy =>
      intro d
      simpa only [add_mul] using J.add_mem (ihx d) (ihy d)
    | neg x hx ih =>
      intro d
      simpa only [neg_mul] using J.neg_mem (ih d)
    | left_absorb c x hx ih =>
      intro d
      simpa only [mul_assoc] using J.mul_mem_left c _ (ih d)
    | right_absorb c x hx ih =>
      intro d
      simpa only [mul_assoc] using ih (c * d)
  have h1 : (1 : A) ∈ TwoSidedIdeal.span {a} := by
    rw [show TwoSidedIdeal.span {a} = ⊤ from ha]
    exact TwoSidedIdeal.mem_top A
  have hbJ : b ∈ J := by simpa using hmul h1 1
  have hk : TwoSidedIdeal.span {b} ≤ J := TwoSidedIdeal.span_le.mpr (by simpa)
  apply top_unique
  rwa [hb] at hk

lemma mem_span_finite {s : Set A} {x : A} (hx : x ∈ TwoSidedIdeal.span s) :
    ∃ t : Finset A, ↑t ⊆ s ∧ x ∈ TwoSidedIdeal.span (t : Set A) := by
  classical
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx => exact ⟨{x}, by simpa, TwoSidedIdeal.subset_span (by simp)⟩
  | zero => exact ⟨∅, by simp, TwoSidedIdeal.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨t, ht, hxt⟩ := ihx
    obtain ⟨u, hu, hyu⟩ := ihy
    refine ⟨t ∪ u, ?_, TwoSidedIdeal.add_mem _ ?_ ?_⟩
    · simpa using Set.union_subset ht hu
    · exact TwoSidedIdeal.span_mono (by simp) hxt
    · exact TwoSidedIdeal.span_mono (by simp) hyu
  | neg x hx ih =>
    obtain ⟨t, ht, hx⟩ := ih
    exact ⟨t, ht, TwoSidedIdeal.neg_mem _ hx⟩
  | left_absorb a x hx ih =>
    obtain ⟨t, ht, hx⟩ := ih
    exact ⟨t, ht, TwoSidedIdeal.mul_mem_left _ _ _ hx⟩
  | right_absorb b x hx ih =>
    obtain ⟨t, ht, hx⟩ := ih
    exact ⟨t, ht, TwoSidedIdeal.mul_mem_right _ _ _ hx⟩

end KirchbergRordam.GenericRW.Fullness
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SignObstruction
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace


open scoped InnerProductSpace
open NormedSpace
namespace KirchbergRordam.GenericRW
namespace DoubleCommutator

lemma derivative_eq_zero_of_concave_bddBelow {f : ℝ → ℝ} {d : ℝ}
    (hc : ConcaveOn ℝ Set.univ f) (hd : HasDerivAt f d 0)
    (M : ℝ) (hM : ∀ t, -M ≤ f t) : d = 0 := by
  have hpos : 0 < M + f 0 + 1 := by linarith [hM 0]
  rcases lt_trichotomy d 0 with hn | he | hp
  · let t := (M + f 0 + 1) / (-d)
    have ht : 0 < t := div_pos hpos (neg_pos.mpr hn)
    have hh := hc.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ t) ht hd
    rw [slope_def_field, sub_zero, div_le_iff₀ ht] at hh
    have htd : d * t = -(M + f 0 + 1) := by
      dsimp [t]
      field_simp [ne_of_lt hn]
    have := hM t
    linarith
  · exact he
  · let t := -(M + f 0 + 1) / d
    have ht : t < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hpos) hp
    have hh := hc.le_slope_of_hasDerivAt (Set.mem_univ t) (Set.mem_univ 0) ht hd
    rw [slope_def_field, zero_sub, le_div_iff₀ (neg_pos.mpr ht)] at hh
    have htd : d * t = -(M + f 0 + 1) := by
      dsimp [t]
      field_simp
    have := hM t
    nlinarith

section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

lemma derivative_orbit (X T : A) (t : ℝ) :
    HasDerivAt (orbit X T) (orbit X (bracket X T) t) t := by
  have hu := hasDerivAt_exp_smul_const X t
  have hv := hasDerivAt_exp_smul_const' (-X) t
  convert (hu.mul_const T).mul hv using 1
  · rfl
  · dsimp only [orbit, bracket]
    noncomm_ring

end BanachAlgebra

section CStar
variable {A : Type*} [CStarAlgebra A]

lemma bracket_smul_left (z : ℂ) (S T : A) :
    bracket (z • S) T = z • bracket S T := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma bracket_smul_right (z : ℂ) (S T : A) :
    bracket S (z • T) = z • bracket S T := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma bracket_I_twice (S T : A) :
    bracket (Complex.I • S) (bracket (Complex.I • S) T) =
      -bracket S (bracket S T) := by
  simp only [bracket_smul_left, bracket_smul_right, smul_smul,
    Complex.I_mul_I, neg_one_smul]

lemma star_rotation (S : A) (hS : IsSelfAdjoint S) (t : ℝ) :
    star (exp (t • (Complex.I • S))) = exp (t • (-(Complex.I • S))) := by
  rw [star_exp]
  congr 1
  simp [star_smul, hS.star_eq, smul_neg]

lemma norm_orbit (S T : A) (hS : IsSelfAdjoint S) (t : ℝ) :
    ‖orbit (Complex.I • S) T t‖ = ‖T‖ := by
  have he (t : ℝ) : exp (t • (Complex.I • S)) =
      (selfAdjoint.expUnitary (t • (⟨S, hS⟩ : selfAdjoint A)) : A) := by
    change exp (t • (Complex.I • S)) = exp (Complex.I • t • S)
    rw [smul_comm]
  rw [orbit, ← star_rotation S hS t, he]
  exact (CStarRing.norm_mul_coe_unitary _ (star _)).trans
    (CStarRing.norm_coe_unitary_mul _ _)

lemma selfAdjoint_I_bracket (S T : A) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (Complex.I • bracket S T) := by
  change star (Complex.I • bracket S T) = Complex.I • bracket S T
  simp only [star_smul, bracket, star_sub, star_mul, hS.star_eq, hT.star_eq,
    Complex.star_def, Complex.conj_I, neg_smul, smul_sub]
  abel

end CStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


omit [CompleteSpace H] in
lemma quadratic_apply (ξ : H) (T : H →L[ℂ] H) :
    quadratic ξ T = (inner ℂ ξ (T ξ)).re := rfl

lemma quadratic_derivative (ξ : H) (X T : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (fun t => quadratic ξ (orbit X T t))
      (quadratic ξ (orbit X (bracket X T) t)) t :=
  (quadratic ξ).hasFDerivAt.comp_hasDerivAt t (derivative_orbit X T t)

lemma quadratic_orbit_lower (ξ : H) (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (t : ℝ) : -(‖quadratic ξ‖ * ‖T‖) ≤ quadratic ξ (orbit (Complex.I • S) T t) := by
  have hn := (quadratic ξ).le_opNorm (orbit (Complex.I • S) T t)
  rw [norm_orbit S T hS t, Real.norm_eq_abs] at hn
  exact (abs_le.mp hn).1

lemma quadratic_orbit_nonneg (ξ : H) (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hT : T.IsPositive) (t : ℝ) : 0 ≤ quadratic ξ (orbit (Complex.I • S) T t) := by
  have hh := (hT.conj_adjoint (exp (t • (Complex.I • S)))).re_inner_nonneg_right ξ
  simpa only [quadratic_apply, orbit, ← star_rotation S hS t,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, RCLike.re_eq_complex_re] using hh

end DoubleCommutator

open DoubleCommutator


theorem commute_of_positive_double_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hz : (S * (S * T - T * S) - (S * T - T * S) * S).IsPositive) :
    Commute S T := by
  have he (ξ : H) : quadratic ξ (Complex.I • bracket S T) = 0 := by
    let X := Complex.I • S
    let f (t : ℝ) := quadratic ξ (orbit X T t)
    let f' (t : ℝ) := quadratic ξ (orbit X (bracket X T) t)
    let f'' (t : ℝ) := quadratic ξ (orbit X (bracket X (bracket X T)) t)
    have hd (t : ℝ) : HasDerivAt f (f' t) t := quadratic_derivative ξ X T t
    have hd' (t : ℝ) : HasDerivAt f' (f'' t) t :=
      quadratic_derivative ξ X (bracket X T) t
    have hneg (t : ℝ) : f'' t ≤ 0 := by
      dsimp only [f'', X]
      rw [bracket_I_twice]
      simp only [orbit, mul_neg, neg_mul, map_neg, neg_nonpos]
      exact quadratic_orbit_nonneg ξ S (bracket S (bracket S T)) hS hz t
    have hc : ConcaveOn ℝ Set.univ f :=
      concaveOn_of_hasDerivWithinAt2_nonpos (convex_univ)
        (fun t _ => (hd t).continuousAt.continuousWithinAt)
        (fun t _ => (hd t).hasDerivWithinAt)
        (fun t _ => (hd' t).hasDerivWithinAt) (fun t _ => hneg t)
    have := derivative_eq_zero_of_concave_bddBelow hc (hd 0)
      (‖quadratic ξ‖ * ‖T‖) (quadratic_orbit_lower ξ S T hS)
    simpa only [f', X, orbit, zero_smul, exp_zero, one_mul, mul_one,
      bracket_smul_left] using this
  have hQ := selfAdjoint_I_bracket S T hS hT
  have h0 : (Complex.I • bracket S T : H →L[ℂ] H).toLinearMap = 0 := by
    apply (inner_map_self_eq_zero _).mp
    intro ξ
    rw [hQ.isSymmetric ξ ξ, ← hQ.isSymmetric.coe_re_inner_self_apply ξ]
    change (quadratic ξ (Complex.I • bracket S T) : ℂ) = 0
    rw [he, Complex.ofReal_zero]
  have h0' : (Complex.I • bracket S T : H →L[ℂ] H) = 0 := by
    ext ξ
    exact congrArg (fun Q : H →ₗ[ℂ] H => Q ξ) h0
  have : bracket S T = 0 := (smul_eq_zero.mp h0').resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mp this


theorem commute_of_negative_double_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hz : (-(S * (S * T - T * S) - (S * T - T * S) * S)).IsPositive) :
    Commute S T := by
  have h := commute_of_positive_double_commutator S (-T) hS hT.neg (by
    convert hz using 1
    noncomm_ring)
  simpa only [Commute, SemiconjBy, mul_neg, neg_mul, neg_inj] using h

end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.Fullness
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma doubleBracket_selfAdjoint (s t : A) (hs : IsSelfAdjoint s) (ht : IsSelfAdjoint t) :
    IsSelfAdjoint (s * (s * t - t * s) - (s * t - t * s) * s) := by
  change star _ = _
  simp only [star_sub, star_mul, hs.star_eq, ht.star_eq]
  noncomm_ring


theorem full_parts (s t : A) (hs : IsSelfAdjoint s) (ht : IsSelfAdjoint t)
    (h : ∀ π : IrreducibleRepresentation A,
      ¬ Commute (π.representation s) (π.representation t)) :
    let z := s * (s * t - t * s) - (s * t - t * s) * s
    IsFull z⁺ ∧ IsFull z⁻ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let z := s * (s * t - t * s) - (s * t - t * s) * s
  have hz : IsSelfAdjoint z := doubleBracket_selfAdjoint s t hs ht
  have he (π : IrreducibleRepresentation A) :
      π.representation z = π.representation z⁺ - π.representation z⁻ := by
    rw [← map_sub, CFC.posPart_sub_negPart z hz]
  constructor
  · apply full_of_survives
    intro π hp
    apply h π
    apply commute_of_negative_double_commutator _ _ (hs.map _) (ht.map _)
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    have hpos : 0 ≤ π.representation z⁻ := map_nonneg π.representation (CFC.negPart_nonneg z)
    have hm : π.representation z =
        π.representation s * (π.representation s * π.representation t -
          π.representation t * π.representation s) -
        (π.representation s * π.representation t - π.representation t * π.representation s) *
          π.representation s := by simp only [z, map_sub, map_mul]
    rw [← hm, he, hp, zero_sub, neg_neg]
    exact hpos
  · apply full_of_survives
    intro π hn
    apply h π
    apply commute_of_positive_double_commutator _ _ (hs.map _) (ht.map _)
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    have hpos : 0 ≤ π.representation z⁺ := map_nonneg π.representation (CFC.posPart_nonneg z)
    have hm : π.representation z =
        π.representation s * (π.representation s * π.representation t -
          π.representation t * π.representation s) -
        (π.representation s * π.representation t - π.representation t * π.representation s) *
          π.representation s := by simp only [z, map_sub, map_mul]
    rw [← hm, he, hn, sub_zero]
    exact hpos

end KirchbergRordam.GenericRW.Fullness
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SpatialTensor
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace


open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.GenericRW.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace H] [CompleteSpace K]

lemma left_right_commute (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    Commute (left (K := K) T) (right (H := H) S) := by
  change map T 1 * map 1 S = map 1 S * map T 1
  rw [← map_mul, ← map_mul]
  simp

end KirchbergRordam.GenericRW.Spatial

namespace KirchbergRordam.GenericRW
namespace MaxTensor
universe u v
variable (A : Type u) (B : Type v) [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]
omit [Nontrivial A] [Nontrivial B] in
lemma nontrivial_of_representations
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial H] [Nontrivial K]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    Nontrivial (Algebra A B) := by
  let φ : A →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    (Spatial.left (K := K)).comp π
  let ψ : B →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    (Spatial.right (H := H)).comp ρ
  have hc : ∀ a b, Commute (φ a) (ψ b) := fun a b =>
    Spatial.left_right_commute (π a) (ρ b)
  let χ : Algebra A B →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    lift (A := A) (B := B)
      (C := Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) φ ψ hc
  exact χ.toRingHom.domain_nontrivial
instance instNontrivialAlgebra : Nontrivial (Algebra A B) := by
  obtain ⟨π⟩ := exists_irreducible_representation A
  obtain ⟨ρ⟩ := exists_irreducible_representation B
  exact nontrivial_of_representations A B π.representation ρ.representation
instance powerPack_nontrivial (D : Type u) [CStarAlgebra D] [Nontrivial D] (n : ℕ) :
    Nontrivial (powerPack D n) := by
  induction n with
  | zero => exact inferInstanceAs (Nontrivial D)
  | succ n ih =>
    let : Nontrivial (powerPack D n) := ih
    exact inferInstanceAs (Nontrivial (Algebra D (powerPack D n)))
end MaxTensor
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.MaxTensor
universe u
variable (D : Type u) [CStarAlgebra D]


theorem exists_joinPower (n m : ℕ) :
    Nonempty (Algebra (powerPack D n) (powerPack D m) →⋆ₐ[ℂ] (powerPack D (n+m+1))) := by
  induction n with
  | zero =>
    rw [Nat.zero_add]
    exact ⟨StarAlgHom.id ℂ (Algebra D (powerPack D m))⟩
  | succ n ih =>
    obtain ⟨φ⟩ := ih
    let ψ := (map (StarAlgHom.id ℂ D) φ).comp
      (TripleTensor.reassociate (A := D) (B := powerPack D n) (C := powerPack D m))
    have he : n + 1 + m + 1 = (n + m + 1) + 1 := by omega
    rw [he]
    exact ⟨ψ⟩
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.Fullness
section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]


theorem finite_bridges {a b : A} (ha : IsFull a) (hb : IsFull b) (hba : b * a = 0) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ c : Fin r → A,
      (∀ i j, c i * c j = 0) ∧ TwoSidedIdeal.span (Set.range c) = ⊤ := by
  classical
  have h1 : (1 : A) ∈ TwoSidedIdeal.span (Set.range (fun d : A => a * d * b)) := by
    rw [bridges_span_one ha hb]
    exact TwoSidedIdeal.mem_top A
  obtain ⟨t, ht, hmem⟩ := mem_span_finite h1
  have hne : t.Nonempty := by
    by_contra he
    have hz : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst t
    have hh : TwoSidedIdeal.span ((↑(∅ : Finset A)) : Set A) ≤ ⊥ :=
      TwoSidedIdeal.span_le.mpr (by simp)
    exact one_ne_zero ((TwoSidedIdeal.mem_bot _).mp (hh hmem))
  let e := Fintype.equivFin t
  let c : Fin (Fintype.card t) → A := fun i => (e.symm i : A)
  refine ⟨Fintype.card t, ?_, c, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hne))
  · intro i j
    obtain ⟨d, hd⟩ := ht (e.symm i).property
    obtain ⟨f, hf⟩ := ht (e.symm j).property
    change (e.symm i : A) * (e.symm j : A) = 0
    rw [← hd, ← hf]
    calc
      a * d * b * (a * f * b) = a * d * (b * a) * f * b := by noncomm_ring
      _ = 0 := by rw [hba]; simp
  · apply TwoSidedIdeal.eq_top
    apply TwoSidedIdeal.span_mono ?_ hmem
    intro z hz
    exact ⟨e ⟨z, hz⟩, by simp [c]⟩
end

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]
lemma full_map {a : A} (ha : IsFull a) (φ : A →⋆ₐ[ℂ] B) : IsFull (φ a) := by
  apply full_of_survives
  intro π
  exact full_survives ha (π.representation.comp φ)
end KirchbergRordam.GenericRW.Fullness

namespace KirchbergRordam.GenericRW.FullSquareZero
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]


lemma orthogonal_of_pair {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (s t : A) (hs : IsSelfAdjoint s) (ht : IsSelfAdjoint t)
    (hp : ∀ π : IrreducibleRepresentation A,
      ¬ Commute (π.representation s) (π.representation t)) :
    ∃ a b : A, IsFull a ∧ IsFull b ∧ b * a = 0 := by
  let z := s * (s * t - t * s) - (s * t - t * s) * s
  have hfull : IsFull z⁺ ∧ IsFull z⁻ := full_parts s t hs ht hp
  exact ⟨z⁺, z⁻, hfull.1, hfull.2, CFC.negPart_mul_posPart z⟩


theorem full_orthogonal_parts (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ n : ℕ, ∃ a b : TripleTensor.Algebra D (powerPack D n) (powerPack D n),
      IsFull a ∧ IsFull b ∧ b * a = 0 := by
  obtain ⟨n, s, t, hs, ht, hp⟩ := NoncommutingPair.exists_pair hD
  refine ⟨n, orthogonal_of_pair s t hs ht ?_⟩
  intro π
  exact hp π.space π.representation π.scalar_commutant

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]


theorem combine_bridges (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ))
    (r : ℕ) (hr : 1 ≤ r) (c : Fin r → A)
    (hcz : ∀ i j, c i * c j = 0) (hcfull : TwoSidedIdeal.span (Set.range c) = ⊤) :
    ∃ n : ℕ, ∃ y : MaxTensor.Algebra A (powerPack D n), y * y = 0 ∧ IsFull y := by
  classical
  obtain ⟨V, hV, hsa, hd⟩ := finite_detecting_space hD
  let := hV
  obtain ⟨n, x, _, hx⟩ := RepresentedLabels.power_labels V hsa hd r hr
  let P := powerPack D n
  let : CStarAlgebra (MaxTensor.Algebra A P) := inferInstance
  let l : A →⋆ₐ[ℂ] MaxTensor.Algebra A P := includeLeft
  let q : P →⋆ₐ[ℂ] MaxTensor.Algebra A P := includeRight
  let y := ∑ i, l (c i) * q (x i)
  refine ⟨n, y, ?_, ?_⟩
  · change (∑ i, l (c i) * q (x i)) * (∑ i, l (c i) * q (x i)) = 0
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [((legs_commute (c i) (x j)).symm).mul_mul_mul_comm]
    rw [← map_mul, hcz, map_zero, zero_mul]
  · apply full_of_survives
    intro π hy
    let α : A →⋆ₐ[ℂ] (π.space →L[ℂ] π.space) := π.representation.comp l
    let β : P →⋆ₐ[ℂ] (π.space →L[ℂ] π.space) := π.representation.comp q
    let M := GroupedFactors.bicommutant α.range
    have hi : LinearIndependent ℂ (fun i => β (x i)) := by
      apply hx π.space A β α
      · intro p a
        exact ((legs_commute a p).map π.representation).symm
      · intro T hq hl
        exact π.scalar_commutant T (commute_of_legs π.representation T hl hq)
    have hrel : ∑ i, α (c i) * β (x i) = 0 := by
      have he : π.representation y = ∑ i, α (c i) * β (x i) := by
        simp only [y, map_sum, map_mul]
        rfl
      rwa [← he]
    have hz := FactorIndependence.relation_coefficients_zero M
      (left_factor π.representation π.scalar_commutant)
      (fun i => α (c i)) (fun i => β (x i))
      (fun i => GroupedFactors.subset_bicommutant _ _ ⟨c i, rfl⟩)
      (fun i => NoncommutingPair.mem_factor_commutant _ _ (by
        rintro z ⟨a, rfl⟩
        exact (legs_commute a (x i)).map π.representation)) hi hrel
    have hk : TwoSidedIdeal.span (Set.range c) ≤ TwoSidedIdeal.ker α.toRingHom := by
      apply TwoSidedIdeal.span_le.mpr
      rintro z ⟨i, rfl⟩
      exact (TwoSidedIdeal.mem_ker _).mpr (hz i)
    have h1 : (1 : A) ∈ TwoSidedIdeal.span (Set.range c) := by
      rw [hcfull]
      exact TwoSidedIdeal.mem_top A
    have hh := (TwoSidedIdeal.mem_ker _).mp (hk h1)
    exact one_ne_zero (by simpa only [map_one] using hh)


theorem exists_full_square_zero_oai (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ n : ℕ, ∃ y : powerPack D n, y * y = 0 ∧ IsFull y := by
  obtain ⟨n, a, b, ha, hb, hba⟩ := full_orthogonal_parts hD
  obtain ⟨r, hr, c, hcz, hcfull⟩ := finite_bridges ha hb hba
  obtain ⟨m, y, hyz, hyfull⟩ := combine_bridges hD r hr c hcz hcfull
  obtain ⟨φ⟩ := exists_joinPower D n n
  let ψ : TripleTensor.Algebra D (powerPack D n) (powerPack D n) →⋆ₐ[ℂ]
      (powerPack D (n+n+1+1)) := MaxTensor.map (StarAlgHom.id ℂ D) φ
  obtain ⟨χ⟩ := exists_joinPower D (n+n+1+1) m
  let θ := χ.comp (MaxTensor.map ψ (StarAlgHom.id ℂ (powerPack D m)))
  refine ⟨n+n+1+1+m+1, θ y, ?_, full_map hyfull θ⟩
  rw [← map_mul, hyz, map_zero]


end KirchbergRordam.GenericRW.FullSquareZero
end

end OAI
end

theorem solution.{u} : type_of% @OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero_oai.{u} := @OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero_oai.{u}
