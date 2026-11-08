-- Prove2me | solution 1 for MarkmanSecant.weil_condition_of_secant_in_hodge_ring
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T07:47:25.571988+00:00
-- url     : https://prove2.me/submissions/f6d30bdb-a8e6-49ee-9ee5-90f1a138cd2d

import Mathlib
import Definitions.Def_MarkmanSecant

/-!
Complete proof of the general Weil condition for Hodge-circle invariant pure spinors.
The proof compares the circle-action trace in two creation-word bases.
Attribution: the MKAux contraction-naturality and J-invariance helpers below are
from fizzyinc3's accepted submission 11519d8d-6234-4150-905e-cf073f5f6def.
All other supporting proofs were developed during this contribution run.
-/

open MarkmanSecant Matrix
open scoped ExteriorAlgebra

namespace MKAux
variable {n : ℕ}

lemma dual_apply (t w : H1 n) : dualLin t w = ∑ i, t i * w i := by
  simp [dualLin, LinearMap.sum_apply, LinearMap.smulRight_apply]

lemma contract_map (f : H1 n →ₗ[ℂ] H1 n) (d : Module.Dual ℂ (H1 n)) (x : Spinor n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) d (ExteriorAlgebra.map f x) =
    ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) (d ∘ₗ f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul]
    have h1 : ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 n)) m) =
        CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 n)) (f m) := ExteriorAlgebra.map_apply_ι f m
    rw [h1, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul, hx, map_sub,
      map_smul, map_mul, h1]
    rfl

lemma cliffAt_apply (s : Spinor n) (v : VC n) :
    cliffAt s v = ExteriorAlgebra.ι ℂ (wPart v) * s +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) (dualLin (tPart v)) s := by
  rfl

/-- The complex structure `J` acting on `H¹`. -/
noncomputable def Jl (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : H1 n →ₗ[ℂ] H1 n :=
  Matrix.mulVecLin (cMat J)

lemma scal_I (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : scal J Complex.I = Jl J := by
  simp [scal, Jl]

lemma cMat_sq (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) :
    cMat J * cMat J = -1 := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ => ((M i j : ℝ) : ℂ)) hJ
  simp only [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul] at h
  simp only [cMat, Matrix.mul_apply, Matrix.map_apply, h]
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply]

lemma hodge_fixed (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (s : Spinor n) (hs : IsInHodgeRing J s) :
    ExteriorAlgebra.map (Jl J) s = s := by
  obtain ⟨c, hc, rfl⟩ := hs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have h := (hc p).2 Complex.I
  rw [scal_I] at h
  rw [h]
  have : Complex.I ^ p * (starRingEnd ℂ) Complex.I ^ p = 1 := by
    rw [← mul_pow, Complex.conj_I]; simp
  rw [this, one_smul]

lemma wPart_IV (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    wPart (IV J *ᵥ v) = cMat J *ᵥ wPart v := by
  ext i
  simp [wPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma tPart_IV (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    tPart (IV J *ᵥ v) = -((cMat J).transpose *ᵥ tPart v) := by
  ext i
  simp [tPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma annih_inv (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) (s : Spinor n)
    (hs : ExteriorAlgebra.map (Jl J) s = s) (v : VC n) (hv : v ∈ annih s) :
    IV J *ᵥ v ∈ annih s := by
  have hv' : cliffAt s v = 0 := hv
  show cliffAt s (IV J *ᵥ v) = 0
  have h0 := congrArg (ExteriorAlgebra.map (Jl J)) hv'
  rw [map_zero, cliffAt_apply, map_add, map_mul, ExteriorAlgebra.map_apply_ι, hs] at h0
  -- the contraction term
  set G : H1 n →ₗ[ℂ] H1 n := -(Jl J) with hG
  have hGJ : G ∘ₗ Jl J = LinearMap.id := by
    apply LinearMap.ext; intro y
    simp only [hG, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, Jl,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, cMat_sq J hJ]
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
  have hc := contract_map (Jl J) (dualLin (tPart v) ∘ₗ G) s
  rw [hs, LinearMap.comp_assoc, hGJ, LinearMap.comp_id] at hc
  rw [← hc] at h0
  rw [cliffAt_apply, wPart_IV, tPart_IV]
  have hd : dualLin (-((cMat J).transpose *ᵥ tPart v)) = dualLin (tPart v) ∘ₗ G := by
    apply LinearMap.ext; intro y
    rw [dual_apply, LinearMap.comp_apply, dual_apply]
    simp only [hG, LinearMap.neg_apply, Jl, Matrix.mulVecLin_apply]
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, neg_mul,
      Finset.sum_neg_distrib, mul_neg, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hd]
  exact h0

end MKAux

set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace WeilSplitting
lemma split_eigen {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0) (hT : ∀ x, T (T x) = a ^ 2 • x) (x : V) :
    ∃ u v, T u = a • u ∧ T v = (-a) • v ∧ u + v = x := by
  let u := (2 * a)⁻¹ • (T x + a • x)
  let v := (2 * a)⁻¹ • (-T x + a • x)
  refine ⟨u, v, ?_, ?_, ?_⟩
  · dsimp [u]
    rw [map_smul, map_add, hT, map_smul]
    module
  · dsimp [v]
    rw [map_smul, map_add, map_neg, hT, map_smul]
    module
  · dsimp [u, v]
    rw [← smul_add]
    have he : (T x + a • x) + (-T x + a • x) = (2 * a) • x := by module
    rw [he, smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) ha), one_smul]

lemma eigenspaces_disjoint {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0) :
    Module.End.eigenspace T a ⊓ Module.End.eigenspace T (-a) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have h1 := Module.End.mem_eigenspace_iff.mp hx.1
  have h2 := Module.End.mem_eigenspace_iff.mp hx.2
  have he : (2 * a) • x = 0 := by
    calc
      _ = a • x - (-a) • x := by module
      _ = 0 := by rw [← h1, ← h2, sub_self]
  exact (smul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) ha)

lemma eigenspaces_span {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0) (hT : ∀ x, T (T x) = a ^ 2 • x) :
    Module.End.eigenspace T a ⊔ Module.End.eigenspace T (-a) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨u, v, hu, hv, he⟩ := split_eigen T a ha hT x
  exact Submodule.mem_sup.mpr ⟨u, Module.End.mem_eigenspace_iff.mpr hu,
    v, Module.End.mem_eigenspace_iff.mpr hv, he⟩

lemma invariant_split {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0) (hT : ∀ x, T (T x) = a ^ 2 • x)
    (S : Submodule ℂ V) (hS : ∀ x ∈ S, T x ∈ S) :
    (S ⊓ Module.End.eigenspace T a) ⊔ (S ⊓ Module.End.eigenspace T (-a)) = S := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro x hx
  let L := T.restrict hS
  have hL (v : S) : L (L v) = a ^ 2 • v := Subtype.ext (hT v.1)
  obtain ⟨u, v, hu, hv, he⟩ := split_eigen L a ha hL ⟨x, hx⟩
  exact Submodule.mem_sup.mpr ⟨u.1, ⟨u.2, Module.End.mem_eigenspace_iff.mpr (congrArg Subtype.val hu)⟩,
    v.1, ⟨v.2, Module.End.mem_eigenspace_iff.mpr (congrArg Subtype.val hv)⟩,
    congrArg Subtype.val he⟩

lemma invariant_finrank {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0) (hT : ∀ x, T (T x) = a ^ 2 • x)
    (S : Submodule ℂ V) (hS : ∀ x ∈ S, T x ∈ S) :
    Module.finrank ℂ S = Module.finrank ℂ ↥(S ⊓ Module.End.eigenspace T a) +
      Module.finrank ℂ ↥(S ⊓ Module.End.eigenspace T (-a)) := by
  have hi : (S ⊓ Module.End.eigenspace T a) ⊓ (S ⊓ Module.End.eigenspace T (-a)) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hh : x ∈ Module.End.eigenspace T a ⊓ Module.End.eigenspace T (-a) := ⟨hx.1.2, hx.2.2⟩
    rwa [eigenspaces_disjoint T a ha] at hh
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (S ⊓ Module.End.eigenspace T a) (S ⊓ Module.End.eigenspace T (-a))
  rw [invariant_split T a ha hT S hS, hi, finrank_bot, add_zero] at h
  exact h

end WeilSplitting

namespace WeilCoordinateForms
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def projector (T : V →ₗ[ℂ] V) (a : ℂ) : V →ₗ[ℂ] V :=
  (2 : ℂ)⁻¹ • (LinearMap.id + a⁻¹ • T)

lemma projector_apply (T : V →ₗ[ℂ] V) (a : ℂ) (x : V) :
    projector T a x = (2 : ℂ)⁻¹ • (x + a⁻¹ • T x) := rfl

lemma projector_add (T : V →ₗ[ℂ] V) (a : ℂ) (x : V) :
    projector T a x + projector T (-a) x = x := by
  simp only [projector_apply, inv_neg, neg_smul]
  module

lemma projector_fix (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0)
    (x : V) (hx : T x = a • x) : projector T a x = x := by
  rw [projector_apply, hx, smul_smul, inv_mul_cancel₀ ha, one_smul]
  module

lemma projector_kill (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0)
    (x : V) (hx : T x = -a • x) : projector T a x = 0 := by
  rw [projector_apply, hx, smul_smul]
  simp [ha]

lemma projector_eigen (T : V →ₗ[ℂ] V) (a : ℂ) (ha : a ≠ 0)
    (hT : ∀ x, T (T x) = a^2 • x) (x : V) :
    T (projector T a x) = a • projector T a x := by
  simp only [projector_apply, map_smul, map_add, hT, smul_smul]
  have hh : a⁻¹ * a^2 = a := by field_simp
  rw [hh]
  simp only [smul_add, smul_smul]
  have hh2 : a * (2 : ℂ)⁻¹ * a⁻¹ = (2 : ℂ)⁻¹ := by field_simp
  rw [hh2]
  module

end WeilCoordinateForms


-- Supporting module: SplitEigenbasis
open WeilSplitting
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SplitEigenbasis

lemma eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (hT : ∀ x, T (T x) = Complex.I ^ 2 • x)
    (S : Submodule ℂ V) (hS : ∀ x ∈ S, T x ∈ S) (r s : ℕ)
    (hplus : Module.finrank ℂ ↥(S ⊓ Module.End.eigenspace T Complex.I) = r)
    (hminus : Module.finrank ℂ ↥(S ⊓ Module.End.eigenspace T (-Complex.I)) = s) :
    ∃ b : Module.Basis (Fin r ⊕ Fin s) ℂ S,
      (∀ i, T (b (Sum.inl i) : V) = Complex.I • (b (Sum.inl i) : V)) ∧
      (∀ i, T (b (Sum.inr i) : V) = (-Complex.I) • (b (Sum.inr i) : V)) := by
  let A := S ⊓ Module.End.eigenspace T Complex.I
  let B := S ⊓ Module.End.eigenspace T (-Complex.I)
  let L : A × B →ₗ[ℂ] S :=
    { toFun := fun v => ⟨v.1.1 + v.2.1, S.add_mem v.1.2.1 v.2.2.1⟩
      map_add' := by intro x y; apply Subtype.ext; dsimp; abel
      map_smul' := by intro c x; apply Subtype.ext; simp [smul_add] }
  have hsurj : Function.Surjective L := by
    intro x
    have hx : x.1 ∈ A ⊔ B := by
      change x.1 ∈ (S ⊓ Module.End.eigenspace T Complex.I) ⊔ (S ⊓ Module.End.eigenspace T (-Complex.I))
      rw [invariant_split T Complex.I Complex.I_ne_zero hT S hS]
      exact x.2
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext he⟩
  have hdim : Module.finrank ℂ (A × B) = Module.finrank ℂ S := by
    rw [Module.finrank_prod, invariant_finrank T Complex.I Complex.I_ne_zero hT S hS]
  let e := LinearEquiv.ofBijective L
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  let a : Module.Basis (Fin r) ℂ A := (Module.finBasis ℂ A).reindex (finCongr hplus)
  let b : Module.Basis (Fin s) ℂ B := (Module.finBasis ℂ B).reindex (finCongr hminus)
  refine ⟨(a.prod b).map e, ?_, ?_⟩
  · intro i
    simp only [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl,
      Function.comp_apply, LinearMap.inl_apply]
    change T ((a i).1 + 0) = Complex.I • ((a i).1 + 0)
    simp only [add_zero]
    exact Module.End.mem_eigenspace_iff.mp (a i).2.2
  · intro i
    simp only [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr,
      Function.comp_apply, LinearMap.inr_apply]
    change T (0 + (b i).1) = (-Complex.I) • (0 + (b i).1)
    simp only [zero_add]
    exact Module.End.mem_eigenspace_iff.mp (b i).2.2

end SplitEigenbasis


-- Supporting module: CliffordFockBasis

open Finset
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CliffordFockBasis
variable {K S : Type*} [Field K] [AddCommGroup S] [Module K S]

/-- Ordered creation words, indexed by the choice to use each creation operator once. -/
def word : (m : ℕ) → (Fin m → S →ₗ[K] S) → S → (Fin m → Bool) → S
  | 0, _, s, _ => s
  | m+1, C, s, q => if q 0 then C 0 (word m (fun i => C i.succ) s (fun i => q i.succ))
    else word m (fun i => C i.succ) s (fun i => q i.succ)

lemma sum_bool_fin {T : Type*} [AddCommMonoid T] {m : ℕ} (f : (Fin (m+1) → Bool) → T) :
    ∑ q, f q = (∑ q, f (Fin.cons true q)) + ∑ q, f (Fin.cons false q) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

lemma kills_word (m : ℕ) (C : Fin m → S →ₗ[K] S) (A : S →ₗ[K] S) (s : S)
    (hs : A s = 0) (hAC : ∀ i x, A (C i x) + C i (A x) = 0)
    (q : Fin m → Bool) : A (word m C s q) = 0 := by
  induction m with
  | zero => exact hs
  | succ m ih =>
    have ht := ih (fun i => C i.succ) (fun i x => hAC i.succ x) (fun i => q i.succ)
    dsimp [word]
    split
    · have h := hAC 0 (word m (fun i => C i.succ) s (fun i => q i.succ))
      rwa [ht, map_zero, add_zero] at h
    · exact ht

lemma independent (m : ℕ) (A C : Fin m → S →ₗ[K] S) (s : S) (hs : s ≠ 0)
    (hAs : ∀ i, A i s = 0)
    (hAC : ∀ i j x, A i (C j x) + C j (A i x) = (if i=j then (1:K) else 0) • x) :
    LinearIndependent K (word m C s) := by
  classical
  induction m with
  | zero =>
    apply Fintype.linearIndependent_iff.mpr
    intro a ha q
    have h : a q • s = 0 := by
      calc
        a q • s = ∑ i, a i • word 0 C s i := by
          rw [Fintype.sum_unique]
          exact congrArg (fun i => a i • s) (Subsingleton.elim _ _)
        _ = 0 := ha
    exact (smul_eq_zero.mp h).resolve_right hs
  | succ m ih =>
    have hind := ih (fun i => A i.succ) (fun i => C i.succ)
      (fun i => hAs i.succ) (fun i j x => by simpa using hAC i.succ j.succ x)
    have hk (q : Fin m → Bool) : A 0 (word m (fun i => C i.succ) s q) = 0 :=
      kills_word m _ _ s (hAs 0) (fun i x => by simpa [Ne.symm (Fin.succ_ne_zero i)] using hAC 0 i.succ x) q
    have hc (q : Fin m → Bool) : A 0 (C 0 (word m (fun i => C i.succ) s q)) = word m (fun i => C i.succ) s q := by
      have h := hAC 0 0 (word m (fun i => C i.succ) s q)
      simpa [hk q] using h
    apply Fintype.linearIndependent_iff.mpr
    intro a ha q
    rw [sum_bool_fin] at ha
    simp only [word, Fin.cons_zero, Fin.cons_succ, Bool.true_eq, ↓reduceIte,
      Bool.false_eq_true] at ha
    have ht : ∀ t, a (Fin.cons true t) = 0 := by
      apply Fintype.linearIndependent_iff.mp hind
      have h := congrArg (A 0) ha
      simpa only [map_add, map_sum, map_smul, hc, hk, smul_zero, sum_const_zero,
        add_zero, map_zero] using h
    have hf : ∀ t, a (Fin.cons false t) = 0 := by
      apply Fintype.linearIndependent_iff.mp hind
      simpa only [ht, zero_smul, sum_const_zero, zero_add] using ha
    have he : q = Fin.cons (q 0) (fun i => q i.succ) := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [he]
    cases h : q 0
    · exact hf _
    · exact ht _

lemma word_eigen (m : ℕ) (C : Fin m → S →ₗ[K] S) (G : S →ₗ[K] S)
    (s : S) (hs : G s = s) (l : Fin m → K)
    (hGC : ∀ i x, G (C i x) = l i • C i (G x)) (q : Fin m → Bool) :
    G (word m C s q) = (∏ i, if q i then l i else 1) • word m C s q := by
  induction m with
  | zero => simpa [word] using hs
  | succ m ih =>
    have ht := ih (fun i => C i.succ) (fun i => l i.succ) (fun i x => hGC i.succ x) (fun i => q i.succ)
    rw [Fin.prod_univ_succ]
    dsimp [word]
    split
    · rw [hGC, ht, map_smul, smul_smul]
    · simpa using ht

lemma sum_weights (m : ℕ) (l : Fin m → K) :
    (∑ q : Fin m → Bool, ∏ i, if q i then l i else 1) = ∏ i, (1 + l i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_bool_fin, Fin.prod_univ_succ]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [← Finset.mul_sum, ih]
    ring

lemma trace_eigenbasis {I : Type*} [Fintype I] (b : Module.Basis I K S)
    (G : S →ₗ[K] S) (l : I → K) (hG : ∀ i, G (b i) = l i • b i) :
    LinearMap.trace K S G = ∑ i, l i := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K b]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, hG, Module.Basis.repr_self]

lemma trace_formula (m : ℕ) (A C : Fin m → S →ₗ[K] S) (s : S) (hs : s ≠ 0)
    (hAs : ∀ i, A i s = 0)
    (hAC : ∀ i j x, A i (C j x) + C j (A i x) = (if i=j then (1:K) else 0) • x)
    (hdim : Module.finrank K S = 2^m)
    (G : S →ₗ[K] S) (hsG : G s = s) (l : Fin m → K)
    (hGC : ∀ i x, G (C i x) = l i • C i (G x)) :
    LinearMap.trace K S G = ∏ i, (1 + l i) := by
  classical
  have hc : Fintype.card (Fin m → Bool) = Module.finrank K S := by simp [hdim]
  let b := basisOfLinearIndependentOfCardEqFinrank (independent m A C s hs hAs hAC) hc
  calc
    LinearMap.trace K S G = ∑ q : Fin m → Bool, ∏ i, if q i then l i else 1 := by
      apply trace_eigenbasis b G _
      intro q
      simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank] using word_eigen m C G s hsG l hGC q
    _ = _ := sum_weights m l

end CliffordFockBasis


-- Supporting module: CliffordFockTrace

open Finset CliffordFockBasis
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CliffordFockTrace
variable {K S : Type*} [Field K] [AddCommGroup S] [Module K S]

lemma trace_formula_indexed {I : Type*} [Fintype I] [DecidableEq I]
    (A C : I → S →ₗ[K] S) (s : S) (hs : s ≠ 0)
    (hAs : ∀ i, A i s = 0)
    (hAC : ∀ i j x, A i (C j x) + C j (A i x) = (if i=j then (1:K) else 0) • x)
    (hdim : Module.finrank K S = 2^Fintype.card I)
    (G : S →ₗ[K] S) (hsG : G s = s) (l : I → K)
    (hGC : ∀ i x, G (C i x) = l i • C i (G x)) :
    LinearMap.trace K S G = ∏ i, (1 + l i) := by
  classical
  let e := Fintype.equivFin I
  have h := trace_formula (Fintype.card I) (fun i => A (e.symm i))
    (fun i => C (e.symm i)) s hs (fun i => hAs (e.symm i))
    (fun i j x => by simpa using hAC (e.symm i) (e.symm j) x)
    hdim G hsG (fun i => l (e.symm i)) (fun i x => hGC (e.symm i) x)
  exact h.trans (e.symm.prod_comp (fun i => 1 + l i))

lemma exterior_finrank {V I : Type*} [AddCommGroup V] [Module K V] [Fintype I] [LinearOrder I]
    (b : Module.Basis I K V) :
    Module.finrank K (ExteriorAlgebra K V) = 2^Fintype.card I := by
  rw [Module.finrank_eq_card_basis b.ExteriorAlgebra]
  exact Fintype.card_finset

lemma exterior_trace {V I : Type*} [AddCommGroup V] [Module K V] [Fintype I] [LinearOrder I]
    (b : Module.Basis I K V) (F : V →ₗ[K] V) (l : I → K)
    (hF : ∀ i, F (b i) = l i • b i) :
    LinearMap.trace K (ExteriorAlgebra K V) (ExteriorAlgebra.map F).toLinearMap = ∏ i, (1+l i) := by
  classical
  let A : I → ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V := fun i =>
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.coord i)
  let C : I → ExteriorAlgebra K V →ₗ[K] ExteriorAlgebra K V := fun i =>
    LinearMap.mulLeft K (ExteriorAlgebra.ι K (b i))
  refine trace_formula_indexed A C (1 : ExteriorAlgebra K V) one_ne_zero
    (fun i => by simp [A]) ?_ (exterior_finrank b) _ (map_one (ExteriorAlgebra.map F)) l ?_
  · intro i j x
    change CliffordAlgebra.contractLeft (b.coord i) (ExteriorAlgebra.ι K (b j) * x) +
      ExteriorAlgebra.ι K (b j) * CliffordAlgebra.contractLeft (b.coord i) x = _
    rw [CliffordAlgebra.contractLeft_ι_mul]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  · intro i x
    change ExteriorAlgebra.map F (ExteriorAlgebra.ι K (b i) * x) =
      l i • (ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.map F x)
    rw [map_mul, ExteriorAlgebra.map_apply_ι, hF, map_smul, smul_mul_assoc]

end CliffordFockTrace


-- Supporting module: MarkmanComplexDimension

set_option backward.isDefEq.respectTransparency false

open MarkmanSecant Matrix

noncomputable section

namespace MarkmanComplexDimension

def imagEigenspace {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    Submodule ℂ (H1 n) := LinearMap.ker ((cMat J).mulVecLin - Complex.I • LinearMap.id)

lemma mem_imagEigenspace {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (v : H1 n) : v ∈ imagEigenspace J ↔ (cMat J).mulVec v = Complex.I • v := by
  change (cMat J).mulVec v - Complex.I • v = 0 ↔ _
  exact sub_eq_zero

lemma finrank_imagEigenspace (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) :
    Module.finrank ℂ (imagEigenspace J) = n := by
  let R : imagEigenspace J →ₗ[ℝ] (Fin (2 * n) → ℝ) :=
    { toFun := fun v i => (v.val i).re
      map_add' := by intro u v; ext i; simp
      map_smul' := by intro r v; ext i; simp }
  have hrel (v : imagEigenspace J) :
      (fun i => (v.val i).im) = -J.mulVec (fun i => (v.val i).re) := by
    have hv := (mem_imagEigenspace J v.val).mp v.property
    ext i
    have hh := congrArg Complex.re (congrFun hv i)
    simp [cMat, Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re] at hh
    change (v.val i).im = -(J.mulVec (fun i => (v.val i).re) i)
    change J.mulVec (fun i => (v.val i).re) i = -(v.val i).im at hh
    linarith
  have hinj : Function.Injective R := by
    intro u v h
    apply Subtype.ext
    funext i
    apply Complex.ext (congrFun h i)
    have hi : (fun i => (u.val i).im) = (fun i => (v.val i).im) := by
      rw [hrel u, hrel v]
      exact congrArg (fun x => -J.mulVec x) h
    exact congrFun hi i
  have hcast (y : Fin (2 * n) → ℝ) :
      (cMat J).mulVec (realH1 y) = realH1 (J.mulVec y) := by
    ext i
    simp [cMat, realH1, Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  have hsurj : Function.Surjective R := by
    intro x
    let z : H1 n := realH1 x - Complex.I • realH1 (J.mulVec x)
    have hsq : J.mulVec (J.mulVec x) = -x := by
      rw [Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
    have hneg : realH1 (-x) = -realH1 x := by ext i; simp [realH1]
    have hz : z ∈ imagEigenspace J := by
      rw [mem_imagEigenspace]
      dsimp only [z]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hcast, hcast, hsq, hneg]
      simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I,
        neg_one_smul, sub_neg_eq_add]
      abel
    refine ⟨⟨z, hz⟩, ?_⟩
    ext i
    simp [R, z, realH1, Complex.mul_re]
  have hr := (LinearEquiv.ofBijective R ⟨hinj, hsurj⟩).finrank_eq
  have ht := Module.finrank_mul_finrank ℝ ℂ (imagEigenspace J)
  rw [Complex.finrank_real_complex] at ht
  rw [Module.finrank_fin_fun] at hr
  omega


end MarkmanComplexDimension


-- Supporting module: MarkmanCircleAction

open MarkmanSecant Matrix MKAux
open scoped ExteriorAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MarkmanCircleAction
variable {n : ℕ}

def op (v : VC n) : Spinor n →ₗ[ℂ] Spinor n :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (wPart v)) +
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) (dualOf (tPart v))

lemma op_apply (v : VC n) (s : Spinor n) : op v s = cliffAt s v := rfl

lemma op_square (v : VC n) (s : Spinor n) :
    op v (op v s) = (tPart v ⬝ᵥ wPart v) • s := by
  change ExteriorAlgebra.ι ℂ (wPart v) * (ExteriorAlgebra.ι ℂ (wPart v) * s +
    CliffordAlgebra.contractLeft (dualOf (tPart v)) s) +
    CliffordAlgebra.contractLeft (dualOf (tPart v)) (ExteriorAlgebra.ι ℂ (wPart v) * s +
    CliffordAlgebra.contractLeft (dualOf (tPart v)) s) = _
  rw [map_add, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_contractLeft,
    mul_add, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_add, add_zero]
  have hd : dualOf (tPart v) (wPart v) = tPart v ⬝ᵥ wPart v := dual_apply _ _
  rw [hd]
  abel

lemma op_add (v w : VC n) : op (v+w) = op v + op w := by
  apply LinearMap.ext
  intro s
  change cliffAt s (v+w) = cliffAt s v + cliffAt s w
  exact map_add _ _ _
lemma op_smul (a : ℂ) (v : VC n) : op (a • v) = a • op v := by
  apply LinearMap.ext
  intro s
  change cliffAt s (a • v) = a • cliffAt s v
  exact map_smul _ _ _

lemma anticommutator (v w : VC n) (s : Spinor n) :
    op v (op w s) + op w (op v s) = pairV v w • s := by
  have h := op_square (v+w) s
  simp only [op_add, LinearMap.add_apply, map_add, op_square] at h
  have hw : wPart (v+w) = wPart v + wPart w := rfl
  have ht : tPart (v+w) = tPart v + tPart w := rfl
  rw [hw,ht,add_dotProduct,dotProduct_add,dotProduct_add] at h
  simp only [add_smul] at h
  unfold pairV
  convert congrArg (fun x : Spinor n => x - ((tPart v ⬝ᵥ wPart v) • s + (tPart w ⬝ᵥ wPart w) • s)) h using 1 <;> module

lemma hodge_circle_fixed (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ)
    (s : Spinor n) (hs : IsInHodgeRing J s) (z : ℂ) (hz : z * star z = 1) :
    ExteriorAlgebra.map (scal J z) s = s := by
  obtain ⟨c,hc,rfl⟩ := hs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [(hc p).2 z]
  change (z^p * (star z)^p) • c p = c p
  rw [← mul_pow,hz,one_pow,one_smul]

lemma scal_apply (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (z : ℂ) (x : H1 n) :
    scal J z x = (z.re : ℂ) • x + (z.im : ℂ) • Jl J x := by
  ext i
  simp [scal, Jl, Complex.real_smul]

lemma J_twice (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1) (x : H1 n) :
    Jl J (Jl J x) = -x := by
  change cMat J *ᵥ (cMat J *ᵥ x) = -x
  rw [Matrix.mulVec_mulVec,cMat_sq J hJ,Matrix.neg_mulVec,Matrix.one_mulVec]

lemma unit_coordinate (z : ℂ) (hz : z * star z = 1) :
    (z.re : ℂ)^2 + (z.im : ℂ)^2 = 1 := by
  have h := congrArg Complex.re hz
  have hh : z.re^2 + z.im^2 = 1 := by simpa [Complex.mul_re,pow_two] using h
  exact_mod_cast hh

end MarkmanCircleAction


-- Supporting module: MarkmanCircleCovariance

open MarkmanSecant Matrix MKAux MarkmanCircleAction
open scoped ExteriorAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MarkmanCircleCovariance
variable {n : ℕ}

lemma scal_conj_comp (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (z : ℂ) (hz : z * star z = 1) :
    (scal J (star z)).comp (scal J z) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change scal J (star z) (scal J z x) = x
  simp only [scal_apply, map_add, map_smul, J_twice J hJ,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_neg]
  have h := unit_coordinate z hz
  match_scalars <;> ring_nf <;> exact h

def scalV (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (z : ℂ) : VC n →ₗ[ℂ] VC n :=
  (z.re : ℂ) • LinearMap.id + (z.im : ℂ) • (IV J).mulVecLin

lemma wPart_scalV (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (z : ℂ) (v : VC n) :
    wPart (scalV J z v) = scal J z (wPart v) := by
  change wPartLin ((z.re : ℂ) • v + (z.im : ℂ) • (IV J *ᵥ v)) = _
  rw [map_add,map_smul,map_smul]
  change (z.re : ℂ) • wPart v + (z.im : ℂ) • wPart (IV J *ᵥ v) = _
  rw [wPart_IV,scal_apply]
  rfl

lemma tPart_scalV (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (z : ℂ) (v : VC n) :
    tPart (scalV J z v) = (z.re : ℂ) • tPart v - (z.im : ℂ) • ((cMat J).transpose *ᵥ tPart v) := by
  change tPartLin ((z.re : ℂ) • v + (z.im : ℂ) • (IV J *ᵥ v)) = _
  rw [map_add,map_smul,map_smul]
  change (z.re : ℂ) • tPart v + (z.im : ℂ) • tPart (IV J *ᵥ v) = _
  rw [tPart_IV]
  module

lemma dual_scalV (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (z : ℂ) (v : VC n) :
    dualLin (tPart (scalV J z v)) = (dualLin (tPart v)).comp (scal J (star z)) := by
  apply LinearMap.ext
  intro y
  rw [LinearMap.comp_apply,dual_apply,dual_apply,tPart_scalV,scal_apply]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_neg]
  change ((z.re : ℂ) • tPart v - (z.im : ℂ) • ((cMat J).transpose *ᵥ tPart v)) ⬝ᵥ y =
    tPart v ⬝ᵥ ((z.re : ℂ) • y + (-(z.im : ℂ)) • (cMat J *ᵥ y))
  rw [sub_dotProduct,smul_dotProduct,smul_dotProduct,dotProduct_add,dotProduct_smul,dotProduct_smul]
  have hd : ((cMat J).transpose *ᵥ tPart v) ⬝ᵥ y = tPart v ⬝ᵥ (cMat J *ᵥ y) := by
    rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec]
  rw [hd]
  simp [smul_eq_mul,sub_eq_add_neg]

lemma equivariant (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (z : ℂ) (hz : z * star z = 1) (v : VC n) (s : Spinor n) :
    ExteriorAlgebra.map (scal J z) (op v s) =
      op (scalV J z v) (ExteriorAlgebra.map (scal J z) s) := by
  change ExteriorAlgebra.map (scal J z) (ExteriorAlgebra.ι ℂ (wPart v)*s +
    CliffordAlgebra.contractLeft (dualOf (tPart v)) s) =
      ExteriorAlgebra.ι ℂ (wPart (scalV J z v))*ExteriorAlgebra.map (scal J z) s +
      CliffordAlgebra.contractLeft (dualOf (tPart (scalV J z v))) (ExteriorAlgebra.map (scal J z) s)
  rw [map_add,map_mul,ExteriorAlgebra.map_apply_ι,wPart_scalV]
  congr 1
  change _ = CliffordAlgebra.contractLeft (dualLin (tPart (scalV J z v))) _
  rw [dual_scalV,contract_map,LinearMap.comp_assoc,scal_conj_comp J hJ z hz,LinearMap.comp_id]
  rfl

end MarkmanCircleCovariance


-- Supporting module: MarkmanEigenGeometry

open MarkmanSecant Matrix MKAux MarkmanCircleAction MarkmanComplexDimension
open WeilSplitting WeilCoordinateForms
open scoped ExteriorAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MarkmanEigenGeometry
variable {n : ℕ}

lemma pair_add_left (x y z : VC n) : pairV (x+y) z = pairV x z + pairV y z := by
  change (tPartLin (x+y)) ⬝ᵥ wPart z + tPart z ⬝ᵥ (wPartLin (x+y)) = _
  rw [map_add,map_add,add_dotProduct,dotProduct_add]
  change tPart x ⬝ᵥ wPart z + tPart y ⬝ᵥ wPart z + (tPart z ⬝ᵥ wPart x + tPart z ⬝ᵥ wPart y) = _
  unfold pairV
  ring
lemma pair_smul_left (a : ℂ) (x y : VC n) : pairV (a • x) y = a * pairV x y := by
  change (tPartLin (a • x)) ⬝ᵥ wPart y + tPart y ⬝ᵥ (wPartLin (a • x)) = _
  rw [map_smul,map_smul,smul_dotProduct,dotProduct_smul]
  change a * (tPart x ⬝ᵥ wPart y) + a * (tPart y ⬝ᵥ wPart x) = _
  simp [pairV,mul_add]
lemma pair_comm (x y : VC n) : pairV x y = pairV y x := add_comm _ _
lemma pair_add_right (x y z : VC n) : pairV x (y+z) = pairV x y + pairV x z := by
  rw [pair_comm,pair_add_left,pair_comm y,pair_comm z]
lemma pair_smul_right (a : ℂ) (x y : VC n) : pairV x (a • y) = a * pairV x y := by
  rw [pair_comm,pair_smul_left,pair_comm]

lemma IV_square (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1) :
    IV J * IV J = -1 := by
  unfold IV
  rw [Matrix.fromBlocks_multiply]
  simp only [neg_mul_neg, mul_zero, zero_mul, add_zero, zero_add,
    ← Matrix.transpose_mul, cMat_sq J hJ, Matrix.transpose_neg, Matrix.transpose_one]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

lemma IV_twice (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1) (x : VC n) :
    (IV J).mulVecLin ((IV J).mulVecLin x) = Complex.I^2 • x := by
  change IV J *ᵥ (IV J *ᵥ x) = _
  rw [Matrix.mulVec_mulVec,IV_square J hJ,Matrix.neg_mulVec,Matrix.one_mulVec,Complex.I_sq,neg_one_smul]

lemma IV_skew (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (x y : VC n) :
    pairV ((IV J).mulVecLin x) y = -pairV x ((IV J).mulVecLin y) := by
  change pairV (IV J *ᵥ x) y = -pairV x (IV J *ᵥ y)
  unfold pairV
  rw [wPart_IV,tPart_IV,wPart_IV,tPart_IV,neg_dotProduct,neg_dotProduct]
  have hx : ((cMat J).transpose *ᵥ tPart x) ⬝ᵥ wPart y = tPart x ⬝ᵥ (cMat J *ᵥ wPart y) := by
    rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec]
  have hy : ((cMat J).transpose *ᵥ tPart y) ⬝ᵥ wPart x = tPart y ⬝ᵥ (cMat J *ᵥ wPart x) := by
    rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec]
  rw [hx,hy]
  ring

lemma h1_plus_dimension (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1) :
    Module.finrank ℂ (Module.End.eigenspace (Jl J) Complex.I) = n := by
  have he : Module.End.eigenspace (Jl J) Complex.I = imagEigenspace J := by
    ext x
    rw [Module.End.mem_eigenspace_iff,mem_imagEigenspace]
    rfl
  rw [he]
  exact finrank_imagEigenspace n J hJ

lemma h1_minus_dimension (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1) :
    Module.finrank ℂ (Module.End.eigenspace (Jl J) (-Complex.I)) = n := by
  have hneg : (-J)*(-J) = -1 := by simpa using hJ
  have hc : cMat (-J) = -cMat J := by ext i j; simp [cMat]
  have he : Module.End.eigenspace (Jl J) (-Complex.I) = imagEigenspace (-J) := by
    ext x
    rw [Module.End.mem_eigenspace_iff,mem_imagEigenspace,hc,Matrix.neg_mulVec]
    change cMat J *ᵥ x = -Complex.I • x ↔ -(cMat J *ᵥ x) = Complex.I • x
    rw [neg_smul]
    constructor <;> intro h
    · rw [h,neg_neg]
    · calc
        _ = -(-(cMat J *ᵥ x)) := (neg_neg _).symm
        _ = _ := congrArg Neg.neg h
  rw [he]
  exact finrank_imagEigenspace n (-J) hneg

end MarkmanEigenGeometry


-- Supporting module: MarkmanDualBasis

open MarkmanSecant Matrix MKAux MarkmanCircleAction MarkmanEigenGeometry
open WeilCoordinateForms
open scoped ExteriorAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MarkmanDualBasis
variable {n : ℕ}

def dualVector (f : VC n →ₗ[ℂ] ℂ) : VC n :=
  Sum.elim (fun i => f (Pi.single (Sum.inr i) 1)) (fun i => f (Pi.single (Sum.inl i) 1))

lemma pair_dualVector (f : VC n →ₗ[ℂ] ℂ) (x : VC n) : pairV x (dualVector f) = f x := by
  have h := congrArg f ((Pi.basisFun ℂ (VIdx n)).sum_repr x)
  have he : f x = ∑ i, x i * f (Pi.single i 1) := by
    simpa [map_sum,map_smul,smul_eq_mul] using h.symm
  rw [he,Fintype.sum_sum_type]
  simp [pairV,dualVector,wPart,tPart,dotProduct,mul_comm,add_comm]

lemma exists_pair_dual {I : Type*} [Fintype I] [DecidableEq I]
    (W : Submodule ℂ (VC n)) (b : Module.Basis I ℂ W) :
    ∃ v : I → VC n, ∀ i j, pairV (b j) (v i) = if j=i then 1 else 0 := by
  classical
  obtain ⟨Z,hZ⟩ := W.exists_isCompl
  let F : I → VC n →ₗ[ℂ] ℂ := fun i => (b.coord i).comp (W.projectionOnto Z hZ)
  refine ⟨fun i => dualVector (F i), ?_⟩
  intro i j
  rw [pair_dualVector]
  change b.coord i (W.projectionOnto Z hZ (b j)) = _
  rw [Submodule.projectionOnto_apply_left]
  simp [Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply]

lemma exists_eigen_dual {I : Type*} [Fintype I] [DecidableEq I]
    (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (W : Submodule ℂ (VC n)) (b : Module.Basis I ℂ W) (a : I → ℂ)
    (ha : ∀ i, a i ≠ 0) (hasq : ∀ i, (a i)^2 = -1)
    (hb : ∀ i, (IV J).mulVecLin (b i) = a i • (b i : VC n)) :
    ∃ v : I → VC n,
      (∀ i j, pairV (b j) (v i) = if j=i then 1 else 0) ∧
      (∀ i, (IV J).mulVecLin (v i) = (-a i) • v i) := by
  classical
  obtain ⟨u,hu⟩ := exists_pair_dual W b
  let v : I → VC n := fun i => projector (IV J).mulVecLin (-a i) (u i)
  refine ⟨v, ?_, ?_⟩
  · intro i j
    have h : pairV (b j) ((IV J).mulVecLin (u i)) = -(a j * pairV (b j) (u i)) := by
      have hh := IV_skew J (b j) (u i)
      rw [hb,pair_smul_left] at hh
      simpa only [neg_neg] using (congrArg Neg.neg hh).symm
    change pairV (b j) (projector (IV J).mulVecLin (-a i) (u i)) = _
    rw [projector_apply,pair_smul_right,pair_add_right,pair_smul_right,h,hu]
    by_cases hij : j=i
    · subst j
      simp only [ite_true,inv_neg]
      field_simp [ha i]
      ring
    · simp [hij]
  · intro i
    exact projector_eigen _ (-a i) (neg_ne_zero.mpr (ha i))
      (fun x => by simpa only [neg_sq,hasq i,Complex.I_sq] using IV_twice J hJ x) (u i)

end MarkmanDualBasis


-- Supporting module: MarkmanTraceComparison

open MarkmanSecant Matrix MKAux MarkmanCircleAction MarkmanEigenGeometry
open MarkmanCircleCovariance CliffordFockTrace WeilSplitting
open scoped ExteriorAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MarkmanTraceComparison
variable {n : ℕ}

lemma spinor_dimension (n : ℕ) : Module.finrank ℂ (Spinor n) = 2^(2*n) := by
  simpa using exterior_finrank (Pi.basisFun ℂ (Fin (2*n)))

lemma scal_eigen_plus (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (z : ℂ)
    (x : H1 n) (hx : Jl J x = Complex.I • x) : scal J z x = z • x := by
  rw [scal_apply,hx,smul_smul,← add_smul,Complex.re_add_im]
lemma scal_eigen_minus (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (z : ℂ)
    (x : H1 n) (hx : Jl J x = -Complex.I • x) : scal J z x = star z • x := by
  rw [scal_apply,hx,smul_smul,← add_smul]
  congr 1
  apply Complex.ext <;> simp

lemma standard_trace (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1) (z : ℂ) :
    LinearMap.trace ℂ (Spinor n) (ExteriorAlgebra.map (scal J z)).toLinearMap =
      (1+z)^n * (1+star z)^n := by
  classical
  letI : LinearOrder (Fin n ⊕ Fin n) := linearOrderOfSTO WellOrderingRel
  have hT : ∀ x, Jl J (Jl J x) = Complex.I^2 • x := by
    intro x
    rw [J_twice J hJ,Complex.I_sq,neg_one_smul]
  obtain ⟨b,hp,hm⟩ := SplitEigenbasis.eigenbasis (Jl J) hT (⊤ : Submodule ℂ (H1 n))
    (fun _ _ => trivial) n n
    (by rw [top_inf_eq]; exact h1_plus_dimension J hJ)
    (by rw [top_inf_eq]; exact h1_minus_dimension J hJ)
  let B : Module.Basis (Fin n ⊕ Fin n) ℂ (H1 n) := b.map (Submodule.topEquiv : (⊤ : Submodule ℂ (H1 n)) ≃ₗ[ℂ] H1 n)
  let l : Fin n ⊕ Fin n → ℂ := Sum.elim (fun _ => z) (fun _ => star z)
  have hB : ∀ i, scal J z (B i) = l i • B i := by
    intro i
    cases i with
    | inl i => exact scal_eigen_plus J z _ (hp i)
    | inr i => exact scal_eigen_minus J z _ (hm i)
  rw [exterior_trace B (scal J z) l hB,Fintype.prod_sum_type]
  simp [l]

end MarkmanTraceComparison


-- Supporting module: MarkmanPureTrace

open MarkmanSecant Matrix MKAux MarkmanCircleAction MarkmanEigenGeometry MarkmanDualBasis
open MarkmanCircleCovariance MarkmanTraceComparison CliffordFockTrace WeilSplitting
open scoped ExteriorAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MarkmanPureTrace
variable {n : ℕ}

def plusDimension (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (s : Spinor n) :=
  Module.finrank ℂ ↥(annih s ⊓ Module.End.eigenspace (IV J).mulVecLin Complex.I)
def minusDimension (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (s : Spinor n) :=
  Module.finrank ℂ ↥(annih s ⊓ Module.End.eigenspace (IV J).mulVecLin (-Complex.I))

lemma annih_invariant (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (s : Spinor n)
    (hs : ∀ z : ℂ, z * star z = 1 → ExteriorAlgebra.map (scal J z) s = s) :
    ∀ v ∈ annih s, (IV J).mulVecLin v ∈ annih s := by
  have h := hs Complex.I (by simp)
  rw [scal_I] at h
  exact MKAux.annih_inv J hJ s h

lemma sum_dimensions (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (s : Spinor n) (hdim : Module.finrank ℂ (annih s) = 2*n)
    (hs : ∀ z : ℂ, z * star z = 1 → ExteriorAlgebra.map (scal J z) s = s) :
    plusDimension J s + minusDimension J s = 2*n := by
  have h := invariant_finrank (IV J).mulVecLin Complex.I Complex.I_ne_zero
    (IV_twice J hJ) (annih s) (annih_invariant J hJ s hs)
  rw [hdim] at h
  exact h.symm

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency true in
lemma annihilator_trace (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (s : Spinor n) (hs0 : s ≠ 0) (hdim : Module.finrank ℂ (annih s) = 2*n)
    (hs : ∀ z : ℂ, z * star z = 1 → ExteriorAlgebra.map (scal J z) s = s)
    (z : ℂ) (hz : z * star z = 1) :
    LinearMap.trace ℂ (Spinor n) (ExteriorAlgebra.map (scal J z)).toLinearMap =
      (1+star z)^(plusDimension J s) * (1+z)^(minusDimension J s) := by
  classical
  let r := plusDimension J s
  let q := minusDimension J s
  let P := annih s
  have hS := annih_invariant J hJ s hs
  obtain ⟨b,hp,hm⟩ := SplitEigenbasis.eigenbasis (IV J).mulVecLin (IV_twice J hJ) P hS r q rfl rfl
  let a : Fin r ⊕ Fin q → ℂ := Sum.elim (fun _ => Complex.I) (fun _ => -Complex.I)
  have ha : ∀ i, a i ≠ 0 := by intro i; cases i <;> simp [a]
  have hasq : ∀ i, (a i)^2 = -1 := by intro i; cases i <;> simp [a]
  have hb : ∀ i, (IV J).mulVecLin (b i) = a i • (b i : VC n) := by
    intro i
    cases i with
    | inl i => exact hp i
    | inr i => exact hm i
  obtain ⟨v,hv,hve⟩ := exists_eigen_dual J hJ P b a ha hasq hb
  let l : Fin r ⊕ Fin q → ℂ := Sum.elim (fun _ => star z) (fun _ => z)
  have hV : ∀ i, scalV J z (v i) = l i • v i := by
    intro i
    change (z.re : ℂ) • v i + (z.im : ℂ) • (IV J).mulVecLin (v i) = _
    rw [hve,smul_smul,← add_smul]
    congr 1
    cases i <;> apply Complex.ext <;> simp [a,l]
  have hAs : ∀ i, op (b i) s = 0 := by
    intro i
    rw [op_apply]
    exact (b i).property
  have hAC : ∀ i j x, op (b i) (op (v j) x) + op (v j) (op (b i) x) =
      (if i=j then (1:ℂ) else 0) • x := by
    intro i j x
    rw [anticommutator,hv]
  have hdimS : Module.finrank ℂ (Spinor n) = 2^Fintype.card (Fin r ⊕ Fin q) := by
    rw [spinor_dimension]
    have h := sum_dimensions J hJ s hdim hs
    change r+q=2*n at h
    simp [h]
  have hG : ∀ i x, ExteriorAlgebra.map (scal J z) (op (v i) x) =
      l i • op (v i) (ExteriorAlgebra.map (scal J z) x) := by
    intro i x
    rw [equivariant J hJ z hz,hV,op_smul,LinearMap.smul_apply]
  have htrace := trace_formula_indexed (K:=ℂ) (S:=Spinor n) (I:=Fin r ⊕ Fin q)
    (fun i => op (n:=n) (b i)) (fun i => op (n:=n) (v i)) s hs0 hAs hAC hdimS
    (ExteriorAlgebra.map (scal J z)).toLinearMap (hs z hz) l hG
  calc
    _ = ∏ i, (1+l i) := htrace
    _ = _ := by rw [Fintype.prod_sum_type]; simp [l,r,q]

end MarkmanPureTrace


-- Supporting module: CircleWeightBalance

set_option backward.isDefEq.respectTransparency false
namespace CircleWeightBalance

lemma balance (n r s : ℕ) (hrs : r+s = 2*n)
    (htrace : ∀ z : ℂ, z * star z = 1 →
      (1+z)^n * (1+star z)^n = (1+star z)^r * (1+z)^s) : r=n ∧ s=n := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2*n+1))
  have hN : 2*n+1 ≠ 0 := by omega
  have hz : IsPrimitiveRoot z (2*n+1) := by
    convert Complex.isPrimitiveRoot_exp (2*n+1) hN using 1 <;> push_cast <;> rfl
  have hunit : z * star z = 1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hz.norm'_eq_one hN]
    norm_num
  have hplus : 1+z ≠ 0 := by
    intro h
    have he : z = -1 := by linear_combination h
    have hpow := hz.pow_eq_one
    rw [he] at hpow
    have hodd : Odd (2*n+1) := ⟨n,rfl⟩
    rw [hodd.neg_one_pow] at hpow
    norm_num at hpow
  have hc : 1+star z ≠ 0 := by
    intro h
    apply hplus
    simpa using congrArg star h
  have he : 1+z = z*(1+star z) := by rw [mul_add,hunit]; ring
  have hh : z^n * (1+star z)^(2*n) = z^s * (1+star z)^(2*n) := by
    calc
      _ = (1+z)^n * (1+star z)^n := by
        rw [he,mul_pow,show 2*n=n+n by omega,pow_add]
        ring
      _ = (1+star z)^r * (1+z)^s := htrace z hunit
      _ = _ := by
        rw [he,mul_pow,← hrs,pow_add]
        ring
  have hns : n=s := hz.pow_inj (by omega) (by omega) (mul_right_cancel₀ (pow_ne_zero _ hc) hh)
  omega

end CircleWeightBalance


-- Supporting module: MarkmanWeilCondition

open MarkmanSecant Matrix MKAux MarkmanCircleAction MarkmanEigenGeometry MarkmanDualBasis
open MarkmanCircleCovariance MarkmanTraceComparison MarkmanPureTrace
open scoped ExteriorAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MarkmanWeilCondition
variable {n : ℕ}

lemma V10_eq (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) :
    Module.End.eigenspace (IV J).mulVecLin Complex.I = V10 J := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  change (IV J).mulVec x = Complex.I • x ↔ (IV J).mulVec x - Complex.I • x = 0
  exact sub_eq_zero.symm
lemma V01_eq (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) :
    Module.End.eigenspace (IV J).mulVecLin (-Complex.I) = V01 J := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  change (IV J).mulVec x = -Complex.I • x ↔ (IV J).mulVec x + Complex.I • x = 0
  rw [neg_smul]
  exact eq_neg_iff_add_eq_zero

lemma balanced_annihilator (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (s : Spinor n) (hs0 : s ≠ 0) (hdim : Module.finrank ℂ (annih s) = 2*n)
    (hs : ∀ z : ℂ, z * star z = 1 → ExteriorAlgebra.map (scal J z) s = s) :
    Module.finrank ℂ ↥(annih s ⊓ V10 J) = n ∧ Module.finrank ℂ ↥(annih s ⊓ V01 J) = n := by
  have h := CircleWeightBalance.balance n (plusDimension J s) (minusDimension J s)
    (sum_dimensions J hJ s hdim hs)
    (fun z hz => (standard_trace J hJ z).symm.trans (annihilator_trace J hJ s hs0 hdim hs z hz))
  unfold plusDimension minusDimension at h
  rw [V10_eq,V01_eq] at h
  exact h

end MarkmanWeilCondition

theorem solution (n : ℕ)
    (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hJ : J*J = -1)
    (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsInHodgeRing J a) (hb : IsInHodgeRing J b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b)) :
    Module.finrank ℂ ↥(annih (a + sqrtNeg d • b) ⊓ V10 J) = n ∧
      Module.finrank ℂ ↥(annih (a - sqrtNeg d • b) ⊓ V10 J) = n ∧
      Module.finrank ℂ ↥(annih (a + sqrtNeg d • b) ⊓ V01 J) = n ∧
      Module.finrank ℂ ↥(annih (a - sqrtNeg d • b) ⊓ V01 J) = n := by
  have hplus := MarkmanWeilCondition.balanced_annihilator J hJ (a + sqrtNeg d • b) h₁.2.1 h₁.2.2
    (fun z hz => by rw [map_add,map_smul,hodge_circle_fixed J a ha z hz,hodge_circle_fixed J b hb z hz])
  have hminus := MarkmanWeilCondition.balanced_annihilator J hJ (a - sqrtNeg d • b) h₂.2.1 h₂.2.2
    (fun z hz => by rw [map_sub,map_smul,hodge_circle_fixed J a ha z hz,hodge_circle_fixed J b hb z hz])
  exact ⟨hplus.1,hminus.1,hplus.2,hminus.2⟩



#print axioms solution
