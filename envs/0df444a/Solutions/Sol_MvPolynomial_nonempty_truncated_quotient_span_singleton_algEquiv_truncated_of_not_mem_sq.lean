-- Prove2me | solution 1 for MvPolynomial.nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bd0f8e20-a847-5be8-9e88-1c044c3bd684

import Mathlib
import Theorems.Thm_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TruncElim

section Generic

open MvPolynomial

variable (k : Type*) [Field k] (e M : ℕ)

local notation "𝔫" => RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)

local notation "T" => MvPolynomial (Fin e) k ⧸ (𝔫) ^ (M + 1)

local notation "𝔱" => Ideal.map (Ideal.Quotient.mk ((𝔫) ^ (M + 1))) (𝔫)

theorem mem_ker_constantCoeff_iff (f : MvPolynomial (Fin e) k) : f ∈ (𝔫) ↔ MvPolynomial.constantCoeff f = 0 :=
  RingHom.mem_ker

theorem X_mem_ker_constantCoeff (j : Fin e) : (MvPolynomial.X j : MvPolynomial (Fin e) k) ∈ (𝔫) := by
  rw [RingHom.mem_ker, MvPolynomial.constantCoeff_X]

theorem ker_constantCoeff_eq_span : (𝔫) = Ideal.span (Set.range (MvPolynomial.X : Fin e → MvPolynomial (Fin e) k)) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    rw [show Set.range (MvPolynomial.X : Fin e → MvPolynomial (Fin e) k) = MvPolynomial.X '' Set.univ by simp,
      MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff] at hm
      exact hm hf
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp this
    exact ⟨i, Set.mem_univ i, hi⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact X_mem_ker_constantCoeff k e j

theorem pow_eq_zero_of_mem (x : T) (hx : x ∈ (𝔱)) : x ^ (M + 1) = 0 := by
  have : x ^ (M + 1) ∈ ((𝔱) ^ (M + 1) : Ideal T) := Ideal.pow_mem_pow hx _
  rwa [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at this

theorem apply_mem_maximalIdeal {C : Type*} [CommRing C] [Algebra k C] [IsLocalRing C]
    (γ : T →ₐ[k] C) (x : T) (hx : x ∈ (𝔱)) : γ x ∈ IsLocalRing.maximalIdeal C := by
  have hnil : IsNilpotent (γ x) := ⟨M + 1, by rw [← map_pow, pow_eq_zero_of_mem k e M x hx, map_zero]⟩
  exact nilradical_le_prime (IsLocalRing.maximalIdeal C) (mem_nilradical.mpr hnil)

variable {k e M}

noncomputable def substAlgHom (P : Fin e → T) (hP : ∀ j, P j ∈ (𝔱)) : T →ₐ[k] T :=
  Ideal.Quotient.liftₐ ((𝔫) ^ (M + 1)) (MvPolynomial.aeval P) (by
    intro f hf

    have hmap : Ideal.map (MvPolynomial.aeval P : MvPolynomial (Fin e) k →ₐ[k] T) (𝔫) ≤ (𝔱) := by
      refine (Ideal.map_mono (le_of_eq (ker_constantCoeff_eq_span k e))).trans ?_
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      simpa using hP j
    have : (MvPolynomial.aeval P) f ∈ Ideal.map (MvPolynomial.aeval P : MvPolynomial (Fin e) k →ₐ[k] T) ((𝔫) ^ (M + 1)) :=
      Ideal.mem_map_of_mem _ hf
    rw [Ideal.map_pow] at this
    have h2 := Ideal.pow_right_mono hmap (M + 1) this
    rwa [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at h2)

@[scoped simp] theorem substAlgHom_mk (P : Fin e → T) (hP : ∀ j, P j ∈ (𝔱)) (f : MvPolynomial (Fin e) k) :
    substAlgHom P hP (Ideal.Quotient.mk _ f) = MvPolynomial.aeval P f := rfl

theorem substAlgHom_X (P : Fin e → T) (hP : ∀ j, P j ∈ (𝔱)) (j : Fin e) :
    substAlgHom P hP (Ideal.Quotient.mk _ (MvPolynomial.X j)) = P j := by
  rw [substAlgHom_mk, MvPolynomial.aeval_X]

end Generic

section Kill

variable (k : Type*) [Field k] (N M : ℕ)

local notation "P₁" => MvPolynomial (Fin (N + 1)) k
local notation "P₀" => MvPolynomial (Fin N) k
local notation "𝔫₁" => RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)
local notation "𝔫₀" => RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)
local notation "T₁" => MvPolynomial (Fin (N + 1)) k ⧸ (𝔫₁) ^ (M + 1)
local notation "T₀" => MvPolynomial (Fin N) k ⧸ (𝔫₀) ^ (M + 1)

noncomputable def killFirst : P₁ →ₐ[k] P₀ := MvPolynomial.aeval (Fin.cases 0 MvPolynomial.X)

variable {k N M}

@[scoped simp] theorem killFirst_X_zero : killFirst k N (MvPolynomial.X 0) = 0 := by
  simp [killFirst]

@[scoped simp] theorem killFirst_X_succ (i : Fin N) : killFirst k N (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [killFirst]

theorem killFirst_rename_succ (p : P₀) : killFirst k N (MvPolynomial.rename Fin.succ p) = p := by
  rw [killFirst, MvPolynomial.aeval_rename]
  have : (Fin.cases (0 : P₀) MvPolynomial.X ∘ Fin.succ : Fin N → P₀) = MvPolynomial.X := funext fun i => by simp
  rw [this, MvPolynomial.aeval_X_left_apply]

theorem killFirst_surjective : Function.Surjective (killFirst k N) :=
  fun p => ⟨MvPolynomial.rename Fin.succ p, killFirst_rename_succ p⟩

theorem killFirst_eq_eval_finSuccEquiv (q : P₁) :
    killFirst k N q = Polynomial.eval 0 (MvPolynomial.finSuccEquiv k N q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [killFirst, MvPolynomial.aeval_C, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      Polynomial.eval_C]
    rfl
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i h =>
    rw [map_mul, map_mul, Polynomial.eval_mul, h]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [killFirst_X_zero, MvPolynomial.finSuccEquiv_X_zero]
    · simp [killFirst_X_succ, MvPolynomial.finSuccEquiv_X_succ]

theorem ker_killFirst : RingHom.ker (killFirst k N) = Ideal.span {MvPolynomial.X 0} := by
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker, killFirst_eq_eval_finSuccEquiv] at hp
    have hdvd : Polynomial.X ∣ MvPolynomial.finSuccEquiv k N p := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact hp
    obtain ⟨q, hq⟩ := hdvd
    have : p = MvPolynomial.X 0 * (MvPolynomial.finSuccEquiv k N).symm q := by
      apply (MvPolynomial.finSuccEquiv k N).injective
      rw [map_mul, MvPolynomial.finSuccEquiv_X_zero, AlgEquiv.apply_symm_apply, hq]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact killFirst_X_zero

theorem map_killFirst_ker : (𝔫₁).map (killFirst k N) = (𝔫₀) := by
  rw [ker_constantCoeff_eq_span k (N + 1), ker_constantCoeff_eq_span k N, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [SetLike.mem_coe, killFirst_X_zero]; exact Ideal.zero_mem _
    · rw [SetLike.mem_coe, killFirst_X_succ]; exact Ideal.subset_span ⟨j, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨MvPolynomial.X j.succ, ⟨j.succ, rfl⟩, killFirst_X_succ j⟩

variable (k N M) in

noncomputable def killFirstT : P₁ →ₐ[k] T₀ :=
  (Ideal.Quotient.mkₐ k ((𝔫₀) ^ (M + 1))).comp (killFirst k N)

theorem killFirstT_surjective : Function.Surjective (killFirstT k N M) :=
  (Ideal.Quotient.mkₐ_surjective k _).comp killFirst_surjective

theorem ker_killFirstT : RingHom.ker (killFirstT k N M) = (𝔫₁) ^ (M + 1) ⊔ Ideal.span {MvPolynomial.X 0} := by
  ext x
  rw [RingHom.mem_ker, killFirstT, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    ← map_killFirst_ker, ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ killFirst_surjective, ← RingHom.ker_eq_comap_bot, ker_killFirst]

variable (k N M) in

noncomputable def quotXZeroEquiv :
    (T₁ ⧸ Ideal.span {(Ideal.Quotient.mk ((𝔫₁) ^ (M + 1)) (MvPolynomial.X 0) : T₁)}) ≃ₐ[k] T₀ :=
  (Ideal.quotientEquivAlgOfEq k (by rw [Ideal.map_span, Set.image_singleton]; rfl)).trans <|
    (DoubleQuot.quotQuotEquivQuotSupₐ k ((𝔫₁) ^ (M + 1)) (Ideal.span {MvPolynomial.X 0})).trans <|
      (Ideal.quotientEquivAlgOfEq k (ker_killFirstT (k := k) (N := N) (M := M)).symm).trans <|
        Ideal.quotientKerAlgEquivOfSurjective killFirstT_surjective

end Kill

end TruncElim
p2m_reactivate "P2MW.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq.TruncElim"

namespace TruncElim

section Main

variable (k : Type*) [Field k] (N M : ℕ)

local notation "P₁" => MvPolynomial (Fin (N + 1)) k
local notation "𝔫₁" => RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)
local notation "𝔫₀" => RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)
local notation "T₁" => MvPolynomial (Fin (N + 1)) k ⧸ (𝔫₁) ^ (M + 1)
local notation "T₀" => MvPolynomial (Fin N) k ⧸ (𝔫₀) ^ (M + 1)
local notation "𝔱₁" => Ideal.map (Ideal.Quotient.mk ((𝔫₁) ^ (M + 1))) (𝔫₁)
local notation "mk₁" => Ideal.Quotient.mk ((𝔫₁) ^ (M + 1))

variable {k N M}

theorem mk_X_mem (j : Fin (N + 1)) : (mk₁ (MvPolynomial.X j) : T₁) ∈ (𝔱₁) :=
  Ideal.mem_map_of_mem _ (X_mem_ker_constantCoeff k (N + 1) j)

theorem tI_eq_span : (𝔱₁) = Ideal.span (Set.range fun j : Fin (N + 1) => (mk₁ (MvPolynomial.X j) : T₁)) := by
  rw [ker_constantCoeff_eq_span k (N + 1), Ideal.map_span, ← Set.range_comp]; rfl

theorem exists_sub_algebraMap_mem (t : T₁) : ∃ a : k, t - algebraMap k T₁ a ∈ (𝔱₁) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨MvPolynomial.constantCoeff p, ?_⟩
  rw [show algebraMap k T₁ (MvPolynomial.constantCoeff p) = mk₁ (MvPolynomial.C (MvPolynomial.constantCoeff p)) from rfl,
    ← map_sub]
  exact Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, map_sub, MvPolynomial.constantCoeff_C, sub_self])

theorem exists_sub_sum_smul_mem_sq (x : T₁) (hx : x ∈ (𝔱₁)) :
    ∃ c : Fin (N + 1) → k, x - ∑ j, c j • (mk₁ (MvPolynomial.X j) : T₁) ∈ (𝔱₁) ^ 2 := by
  classical
  rw [tI_eq_span] at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
  choose c hc using fun j => exists_sub_algebraMap_mem (a j)
  refine ⟨c, ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def, ← sub_mul, pow_two]
  exact Ideal.mul_mem_mul (hc j) (mk_X_mem j)

variable (k N M) in

theorem main (x : T₁) (hx₁ : x ∈ (𝔱₁)) (hx₂ : x ∉ (𝔱₁) ^ 2) :
    Nonempty ((T₁ ⧸ Ideal.span ({x} : Set T₁)) ≃ₐ[k] T₀) := by
  classical

  obtain ⟨c, hc⟩ := exists_sub_sum_smul_mem_sq x hx₁
  have hc0 : ∃ j₀, c j₀ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx₂
    have : ∑ j, c j • (mk₁ (MvPolynomial.X j) : T₁) = 0 := Finset.sum_eq_zero fun j _ => by rw [h j, zero_smul]
    rw [this, sub_zero] at hc
    exact hc
  obtain ⟨j₀, hj₀⟩ := hc0

  let τ : Equiv.Perm (Fin (N + 1)) := Equiv.swap 0 j₀
  let Pσ : Fin (N + 1) → T₁ := fun i => if i = 0 then x else mk₁ (MvPolynomial.X (τ i))
  have hPσ : ∀ i, Pσ i ∈ (𝔱₁) := fun i => by
    by_cases hi : i = 0
    · simp only [Pσ, hi, if_true]; exact hx₁
    · simp only [Pσ, hi, if_false]; exact mk_X_mem _
  let σ : T₁ →ₐ[k] T₁ := substAlgHom Pσ hPσ
  have hσX0 : σ (mk₁ (MvPolynomial.X 0)) = x := by
    rw [substAlgHom_X]; simp [Pσ]
  have hσXτ : ∀ m : Fin (N + 1), m ≠ j₀ → σ (mk₁ (MvPolynomial.X (τ m))) = mk₁ (MvPolynomial.X m) := by
    intro m hm
    have hτm : τ m ≠ 0 := by
      intro h
      have := congrArg τ h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact hm this
    rw [substAlgHom_X]
    simp only [Pσ, hτm, if_false]
    rw [Equiv.swap_apply_self]

  have honto : ∀ j : Fin (N + 1), ∃ t, σ t - mk₁ (MvPolynomial.X j) ∈ (𝔱₁) ^ 2 := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      refine ⟨(c j)⁻¹ • (mk₁ (MvPolynomial.X 0) - ∑ m ∈ Finset.univ.erase j, c m • mk₁ (MvPolynomial.X (τ m))), ?_⟩
      rw [map_smul, map_sub, map_sum, hσX0]
      have hsum : ∑ m ∈ Finset.univ.erase j, σ (c m • mk₁ (MvPolynomial.X (τ m))) =
          ∑ m ∈ Finset.univ.erase j, c m • (mk₁ (MvPolynomial.X m) : T₁) :=
        Finset.sum_congr rfl fun m hm => by rw [map_smul, hσXτ m (Finset.ne_of_mem_erase hm)]
      rw [hsum]
      have key : (c j)⁻¹ • (x - ∑ m ∈ Finset.univ.erase j, c m • (mk₁ (MvPolynomial.X m) : T₁)) - mk₁ (MvPolynomial.X j) =
          (c j)⁻¹ • (x - ∑ m, c m • (mk₁ (MvPolynomial.X m) : T₁)) := by
        rw [← Finset.add_sum_erase Finset.univ (fun m => c m • (mk₁ (MvPolynomial.X m) : T₁)) (Finset.mem_univ j)]
        rw [smul_sub, smul_sub, smul_add, sub_add_eq_sub_sub, smul_smul, inv_mul_cancel₀ hj₀, one_smul]
        abel
      rw [key]
      exact Submodule.smul_of_tower_mem _ _ hc
    · exact ⟨mk₁ (MvPolynomial.X (τ j)), by rw [hσXτ j hj, sub_self]; exact Ideal.zero_mem _⟩

  have hbij := MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq k (N + 1) M σ honto
  let σ' : T₁ ≃ₐ[k] T₁ := AlgEquiv.ofBijective σ hbij
  have hmap : Ideal.span ({x} : Set T₁) =
      (Ideal.span {(mk₁ (MvPolynomial.X 0) : T₁)}).map (σ' : T₁ →+* T₁) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact hσX0.symm
  exact ⟨(Ideal.quotientEquivAlg (Ideal.span {(mk₁ (MvPolynomial.X 0) : T₁)}) (Ideal.span ({x} : Set T₁)) σ' hmap).symm.trans
    (quotXZeroEquiv k N M)⟩

end Main
p2m_reactivate "P2MW.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq.TruncElim"

end TruncElim
p2m_reactivate "P2MW.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq.TruncElim"

open TruncElim in

theorem solution
    (k : Type*) [Field k] (N M : ℕ)
    (x : (MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
    (hx₁ : x ∈ Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)))
    (hx₂ : x ∉ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k))) ^ 2) :
    Nonempty (((MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)) ⧸ Ideal.span ({x} : Set _)) ≃ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1))) :=
  TruncElim.main k N M x hx₁ hx₂

end S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq
end P2MW
export P2MW.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq (solution)
