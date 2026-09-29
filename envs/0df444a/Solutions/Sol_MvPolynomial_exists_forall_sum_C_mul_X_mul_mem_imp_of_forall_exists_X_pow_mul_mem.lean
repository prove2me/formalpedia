-- Prove2me | solution 1 for MvPolynomial.exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ce2cdaf9-2643-5397-a4ab-32dc8659e52b

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
import Theorems.Thm_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
import Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace D2SOL

variable (n : ℕ) (K : Type) [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hc_eq (p : MvPolynomial (Fin (n + 1)) K) (k : ℕ) :
    homogeneousComponent k p = (DirectSum.decompose 𝒜 p k : MvPolynomial (Fin (n + 1)) K) := by
  rw [← DirectSum.Decomposition.decompose'_eq, MvPolynomial.decomposition.decompose'_apply]

theorem hc_mul_left {a b : MvPolynomial (Fin (n + 1)) K} {i : ℕ} (ha : a.IsHomogeneous i) (j : ℕ) :
    homogeneousComponent (i + j) (a * b) = a * homogeneousComponent j b := by
  rw [hc_eq, hc_eq]
  exact DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (b := b) ((mem_homogeneousSubmodule i a).2 ha)

theorem homogeneousComponent_mem_of_span (d : ℕ)
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span s) :
    ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have hhom : (Ideal.span s).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
    Ideal.homogeneous_span _ _ fun p hp => ⟨d, (mem_homogeneousSubmodule d p).2 (hs p hp)⟩
  intro p hp i
  have := hhom i hp
  rwa [← DirectSum.Decomposition.decompose'_eq, MvPolynomial.decomposition.decompose'_apply] at this

theorem finite_homog (e : ℕ) : Module.Finite K ↥(𝒜 e) := by
  have hfin : Set.Finite {d : Fin (n + 1) →₀ ℕ | d.degree = e} :=
    (Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset fun d hd => le_of_eq hd
  haveI : Finite ↥{d : Fin (n + 1) →₀ ℕ | d.degree = e} := hfin.to_subtype
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp _).symm

noncomputable def Ipart (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) : Submodule K ↥(𝒜 e) :=
  Submodule.comap (𝒜 e).subtype (I.restrictScalars K)

theorem mem_Ipart {I : Ideal (MvPolynomial (Fin (n + 1)) K)} {e : ℕ} (x : ↥(𝒜 e)) :
    x ∈ Ipart n K I e ↔ (x : MvPolynomial (Fin (n + 1)) K) ∈ I := Iff.rfl

theorem finrank_piece_add (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K (piece I e) + Module.finrank K (Ipart n K I e) = Module.finrank K ↥(𝒜 e) := by
  haveI := finite_homog n K e
  exact Submodule.finrank_quotient_add_finrank _

theorem finrank_piece_le_of_le {I I' : Ideal (MvPolynomial (Fin (n + 1)) K)} (h : I ≤ I') (e : ℕ) :
    Module.finrank K (piece I' e) ≤ Module.finrank K (piece I e) := by
  haveI := finite_homog n K e
  have h1 := finrank_piece_add n K I e
  have h2 := finrank_piece_add n K I' e
  have h3 : Module.finrank K (Ipart n K I e) ≤ Module.finrank K (Ipart n K I' e) :=
    Submodule.finrank_mono fun x hx => h hx
  omega

theorem Ipart_eq_of_le_of_finrank_eq {I I' : Ideal (MvPolynomial (Fin (n + 1)) K)} (h : I ≤ I') (e : ℕ)
    (he : Module.finrank K (piece I' e) = Module.finrank K (piece I e)) :
    Ipart n K I e = Ipart n K I' e := by
  haveI := finite_homog n K e
  have h1 := finrank_piece_add n K I e
  have h2 := finrank_piece_add n K I' e
  exact Submodule.eq_of_le_of_finrank_eq (fun x hx => h hx) (by omega)

theorem main [Infinite K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hsat : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∀ i : Fin (n + 1), ∃ N : ℕ, X i ^ N * F ∈ I) → F ∈ I) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
        (∑ i, C (a i) * X i) * F ∈ I → F ∈ I := by
  classical
  set H : ℕ → ℕ := fun d => Module.finrank K (piece I d) with hH
  have hmac : ∀ d, 1 ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d) := fun d hd =>
    MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd K I hI
  obtain ⟨D₀, hD₀⟩ := Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow H 1 le_rfl hmac
  set m : ℕ := max D₀ 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hgrow : ∀ e, m ≤ e → H (e + 1) = Nat.macaulayPow e (H e) := fun e he =>
    hD₀ e ((le_max_left _ _).trans he)

  set s : Set (MvPolynomial (Fin (n + 1)) K) := {p | p ∈ I ∧ p.IsHomogeneous m} with hs
  set J : Ideal (MvPolynomial (Fin (n + 1)) K) := Ideal.span s with hJ
  have hJs : ∃ s' : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s', p.IsHomogeneous m) ∧ J = Ideal.span s' :=
    ⟨s, fun p hp => hp.2, rfl⟩
  have hJI : J ≤ I := Ideal.span_le.2 fun p hp => hp.1
  have hJh : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := homogeneousComponent_mem_of_span n K m J hJs

  have hIm : Ipart n K J m = Ipart n K I m := by
    apply le_antisymm
    · exact fun x hx => hJI hx
    · intro x hx
      have hx' : (x : MvPolynomial (Fin (n + 1)) K) ∈ I := hx
      show (x : MvPolynomial (Fin (n + 1)) K) ∈ J
      exact Ideal.subset_span ⟨hx', (mem_homogeneousSubmodule m _).1 x.2⟩
  have hHm : Module.finrank K (piece J m) = H m := by
    have h1 := finrank_piece_add n K J m
    have h2 := finrank_piece_add n K I m
    rw [hIm] at h1
    simp only [hH]
    omega

  have hmaxJ : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m)) := by
    apply le_antisymm
    · exact MvPolynomial.finrank_piece_succ_le_macaulayPow n m hm1 K J hJh
    · rw [hHm, ← hgrow m le_rfl]
      exact finrank_piece_le_of_le n K hJI (m + 1)

  have hpers := MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    n m hm1 K J hJs hmaxJ

  have hHJ : ∀ k : ℕ, Module.finrank K (piece J (m + k)) = H (m + k) := by
    intro k
    induction k with
    | zero => simpa using hHm
    | succ k ih =>
        rw [← add_assoc, hpers (m + k) (Nat.le_add_right m k), ih, ← hgrow (m + k) (Nat.le_add_right m k)]
  have hIJ : ∀ e, m ≤ e → Ipart n K J e = Ipart n K I e := by
    intro e he
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
    exact Ipart_eq_of_le_of_finrank_eq n K hJI (m + k) (hHJ k).symm
  have hmemIJ : ∀ e, m ≤ e → ∀ F : MvPolynomial (Fin (n + 1)) K, F.IsHomogeneous e → F ∈ I → F ∈ J := by
    intro e he F hF hFI
    have hx : (⟨F, (mem_homogeneousSubmodule e F).2 hF⟩ : ↥(𝒜 e)) ∈ Ipart n K I e := hFI
    rw [← hIJ e he] at hx
    exact hx

  obtain ⟨G, hG0, hG⟩ :=
    MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow n m K J hJs hmaxJ
  refine ⟨G, hG0, fun a ha d F hF hlF => ?_⟩
  have hℓ : (∑ i, C (a i) * X i : MvPolynomial (Fin (n + 1)) K).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_C (Fin (n + 1)) (a i)).mul (isHomogeneous_X K i)
  apply hsat d F hF
  intro i
  refine ⟨m, ?_⟩
  have hdeg : (X i ^ m * F).IsHomogeneous (m + d) := (isHomogeneous_X_pow i m).mul hF
  have h1 : (∑ i, C (a i) * X i) * (X i ^ m * F) ∈ I := by
    rw [mul_left_comm]
    exact I.mul_mem_left _ hlF
  have h2 : (∑ i, C (a i) * X i) * (X i ^ m * F) ∈ J :=
    hmemIJ (1 + (m + d)) (by omega) _ (hℓ.mul hdeg) h1
  exact hJI (hG a ha (m + d) (by omega) _ hdeg h2)

theorem exists_eval_ne_zero [Infinite K] {G : MvPolynomial (Fin (n + 1)) K} (hG : G ≠ 0) :
    ∃ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 := by
  by_contra h
  push Not at h
  exact hG (MvPolynomial.funext fun a => by rw [h a, map_zero])

end D2SOL

theorem solution
    (n : ℕ) (K : Type) [Field K] [Infinite K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (hsat : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) → F ∈ I) :
    ∃ a : Fin (n + 1) → K, ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
      (∑ i : Fin (n + 1), MvPolynomial.C (a i) * MvPolynomial.X i) * F ∈ I → F ∈ I := by
  obtain ⟨G, hG0, hG⟩ := D2SOL.main n K I hI hsat
  obtain ⟨a, ha⟩ := D2SOL.exists_eval_ne_zero n K hG0
  exact ⟨a, hG a ha⟩

end S_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem
end P2MW
export P2MW.S_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem (solution)
