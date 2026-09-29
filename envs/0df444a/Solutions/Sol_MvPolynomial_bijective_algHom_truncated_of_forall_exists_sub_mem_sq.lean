-- Prove2me | solution 1 for MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/83e375bc-bf0d-5af4-b105-3c09f8da7837

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq

set_option autoImplicit false

namespace TruncIFT

open MvPolynomial

variable (k : Type*) [Field k] (N M : ℕ)

local notation "P" => MvPolynomial (Fin N) k
local notation "𝔫" => RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)
local notation "T" => MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)
local notation "𝔱" => Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
  (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k))

theorem ker_constantCoeff_eq_span : (𝔫 : Ideal P) = Ideal.span (Set.range (X : Fin N → P)) := by
  ext f
  rw [RingHom.mem_ker, ← Set.image_univ, mem_ideal_span_X_image, constantCoeff_eq, ← notMem_support_iff]
  constructor
  · intro h m hm
    by_contra hne
    push Not at hne
    have : m = 0 := Finsupp.ext fun i => by simpa using hne i (Set.mem_univ i)
    exact h (this ▸ hm)
  · intro h h0
    obtain ⟨i, -, hi⟩ := h 0 h0
    exact hi rfl

theorem mk_X_mem_t (j : Fin N) : (Ideal.Quotient.mk _ (X j) : T) ∈ (𝔱 : Ideal T) :=
  Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, constantCoeff_X])

theorem t_eq_span : (𝔱 : Ideal T) = Ideal.span (Set.range fun j : Fin N => (Ideal.Quotient.mk _ (X j) : T)) := by
  rw [ker_constantCoeff_eq_span, Ideal.map_span, ← Set.range_comp]
  rfl

theorem t_pow_eq_bot : (𝔱 : Ideal T) ^ (M + 1) = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem exists_eq_algebraMap_add (t : T) : ∃ (c : k) (u : T), u ∈ (𝔱 : Ideal T) ∧ t = algebraMap k T c + u := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨constantCoeff f, Ideal.Quotient.mk _ (f - C (constantCoeff f)), Ideal.mem_map_of_mem _ ?_, ?_⟩
  · rw [RingHom.mem_ker, map_sub, constantCoeff_C, sub_self]
  · rw [map_sub, IsScalarTower.algebraMap_apply k P T, algebraMap_eq, Ideal.Quotient.algebraMap_eq,
      add_sub_cancel]

theorem eq_top_of_forall_X (S : Subalgebra k T)
    (hS : ∀ j : Fin N, ∃ s ∈ S, s - Ideal.Quotient.mk _ (X j) ∈ (𝔱 : Ideal T) ^ 2) : S = ⊤ := by
  classical
  let V : Submodule k T := Subalgebra.toSubmodule S
  let I : ℕ → Submodule k T := fun n => ((𝔱 : Ideal T) ^ n).restrictScalars k
  have hI : ∀ n (t : T), t ∈ I n ↔ t ∈ (𝔱 : Ideal T) ^ n := fun n t => Iff.rfl

  have hA : ∀ t : T, t ∈ (𝔱 : Ideal T) → t ∈ V ⊔ I 2 := by
    intro t ht
    rw [t_eq_span, Ideal.mem_span_range_iff_exists_fun] at ht
    obtain ⟨c, rfl⟩ := ht
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨κ, u, hu, hc⟩ := exists_eq_algebraMap_add k N M (c j)
    obtain ⟨s, hs, hsr⟩ := hS j

    have : c j * Ideal.Quotient.mk _ (X j) =
        κ • s + (κ • (Ideal.Quotient.mk _ (X j) - s) + u * Ideal.Quotient.mk _ (X j)) := by
      rw [hc, Algebra.smul_def, Algebra.smul_def]; ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (S.smul_mem hs κ)) (Submodule.mem_sup_right ?_)
    rw [hI]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← neg_sub, smul_neg]
      exact neg_mem (Submodule.smul_of_tower_mem _ κ hsr)
    · rw [show ((𝔱 : Ideal T) ^ 2) = (𝔱 : Ideal T) * (𝔱 : Ideal T) from pow_two _]
      exact Ideal.mul_mem_mul hu (mk_X_mem_t k N M j)

  have hB : ∀ n, 1 ≤ n → ∀ t : T, t ∈ (𝔱 : Ideal T) ^ n → t ∈ V ⊔ I (n + 1) := by
    intro n hn
    induction n with
    | zero => exact absurd hn (by norm_num)
    | succ n ih =>
      intro t ht
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · simpa using hA t (by simpa using ht)
      rw [show (𝔱 : Ideal T) ^ (n + 1) = (𝔱 : Ideal T) * (𝔱 : Ideal T) ^ n from Ideal.IsTwoSided.pow_succ _] at ht
      refine Submodule.mul_induction_on ht (fun a ha b hb => ?_) (fun x y hx hy => Submodule.add_mem _ hx hy)
      obtain ⟨v, hv, a', ha', rfl⟩ := Submodule.mem_sup.mp (hA a ha)
      obtain ⟨w, hw, b', hb', rfl⟩ := Submodule.mem_sup.mp (ih hnpos b hb)
      rw [hI] at ha' hb'
      have hvJ : v ∈ (𝔱 : Ideal T) := by
        have : v + a' - a' ∈ (𝔱 : Ideal T) := Ideal.sub_mem _ ha (Ideal.pow_le_self two_ne_zero ha')
        simpa using this
      have hwJ : w ∈ (𝔱 : Ideal T) ^ n := by
        have : w + b' - b' ∈ (𝔱 : Ideal T) ^ n :=
          Ideal.sub_mem _ hb (Ideal.pow_le_pow_right (Nat.le_succ n) hb')
        simpa using this
      have hexp : (v + a') * (w + b') = v * w + (v * b' + a' * w + a' * b') := by ring
      rw [hexp]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (S.mul_mem hv hw)) (Submodule.mem_sup_right ?_)
      rw [hI]
      have h1 : v * b' ∈ (𝔱 : Ideal T) ^ (n + 1 + 1) := by
        rw [show (𝔱 : Ideal T) ^ (n + 1 + 1) = (𝔱 : Ideal T) * (𝔱 : Ideal T) ^ (n + 1) from Ideal.IsTwoSided.pow_succ _]
        exact Ideal.mul_mem_mul hvJ hb'
      have h2 : a' * w ∈ (𝔱 : Ideal T) ^ (n + 1 + 1) := by
        rw [show (𝔱 : Ideal T) ^ (n + 1 + 1) = (𝔱 : Ideal T) ^ 2 * (𝔱 : Ideal T) ^ n from by
          rw [← Ideal.IsTwoSided.pow_add]; congr 1; omega]
        exact Ideal.mul_mem_mul ha' hwJ
      have h3 : a' * b' ∈ (𝔱 : Ideal T) ^ (n + 1 + 1) := by
        have : a' * b' ∈ (𝔱 : Ideal T) ^ 2 * (𝔱 : Ideal T) ^ (n + 1) := Ideal.mul_mem_mul ha' hb'
        rw [← Ideal.IsTwoSided.pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
      exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3

  have hC : ∀ d n, 1 ≤ n → n + d = M + 1 → ∀ t : T, t ∈ (𝔱 : Ideal T) ^ n → t ∈ V := by
    intro d
    induction d with
    | zero =>
      intro n hn hnd t ht
      rw [add_zero] at hnd
      rw [hnd, t_pow_eq_bot] at ht
      rw [(Submodule.mem_bot T).mp ht]; exact Submodule.zero_mem _
    | succ d ih =>
      intro n hn hnd t ht
      obtain ⟨v, hv, t', ht', rfl⟩ := Submodule.mem_sup.mp (hB n hn t ht)
      exact Submodule.add_mem _ hv (ih (n + 1) (by omega) (by omega) t' ht')

  refine eq_top_iff.mpr fun t _ => ?_
  obtain ⟨c, u, hu, rfl⟩ := exists_eq_algebraMap_add k N M t
  have huV : u ∈ V := hC M 1 le_rfl (by omega) u (by simpa using hu)
  exact S.add_mem (S.algebraMap_mem c) huV

theorem moduleFinite : Module.Finite k T := by
  classical
  have hint : ∀ t ∈ Set.range (fun j : Fin N => (Ideal.Quotient.mk _ (X j) : T)), IsIntegral k t := by
    rintro _ ⟨j, rfl⟩
    refine ⟨Polynomial.X ^ (M + 1), Polynomial.monic_X_pow _, ?_⟩
    rw [Polynomial.eval₂_X_pow]
    have : (Ideal.Quotient.mk _ (X j) : T) ^ (M + 1) ∈ (𝔱 : Ideal T) ^ (M + 1) :=
      Ideal.pow_mem_pow (mk_X_mem_t k N M j) _
    rwa [t_pow_eq_bot, Ideal.mem_bot] at this
  have hfin : Module.Finite k (Algebra.adjoin k (Set.range fun j : Fin N => (Ideal.Quotient.mk _ (X j) : T))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) hint
  have htop : Algebra.adjoin k (Set.range fun j : Fin N => (Ideal.Quotient.mk _ (X j) : T)) = ⊤ := by
    have h0 := MvPolynomial.adjoin_range_X (R := k) (σ := Fin N)
    have h1 := congrArg (Subalgebra.map (Ideal.Quotient.mkₐ k ((𝔫 : Ideal P) ^ (M + 1)))) h0
    rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
      (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective k _)] at h1
    exact h1
  rw [htop] at hfin
  exact Module.Finite.of_surjective (⊤ : Subalgebra k T).val.toLinearMap (fun t => ⟨⟨t, Algebra.mem_top⟩, rfl⟩)

theorem main (θ : T →ₐ[k] T)
    (hθ : ∀ j : Fin N, ∃ t, θ t - Ideal.Quotient.mk _ (X j) ∈ (𝔱 : Ideal T) ^ 2) :
    Function.Bijective θ := by
  haveI := moduleFinite k N M
  have hsurj : Function.Surjective θ := by
    have htop := eq_top_of_forall_X k N M θ.range (fun j => by
      obtain ⟨t, ht⟩ := hθ j
      exact ⟨θ t, ⟨t, rfl⟩, ht⟩)
    intro y
    have hy : y ∈ θ.range := by rw [htop]; exact Algebra.mem_top
    exact hy
  exact ⟨(LinearMap.injective_iff_surjective (f := θ.toLinearMap)).mpr hsurj, hsurj⟩

end TruncIFT

theorem solution
    (k : Type*) [Field k] (N M : ℕ)
    (θ : (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)) →ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
    (hθ : ∀ j : Fin N, ∃ t, θ t - Ideal.Quotient.mk _ (MvPolynomial.X j) ∈
      (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k))) ^ 2) :
    Function.Bijective θ :=
  TruncIFT.main k N M θ hθ

end S_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq
end P2MW
export P2MW.S_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq (solution)
