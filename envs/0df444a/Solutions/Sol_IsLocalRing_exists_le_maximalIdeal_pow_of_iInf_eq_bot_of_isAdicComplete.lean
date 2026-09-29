-- Prove2me | solution 1 for IsLocalRing.exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/41f48385-9816-5f3c-baa4-00cc9965bdb8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete

set_option autoImplicit false

universe u

open IsLocalRing

namespace ChevalleyE95

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

local notation "𝔪" => IsLocalRing.maximalIdeal A

theorem iInf_sup_pow_eq (K : Ideal A) : ⨅ k : ℕ, (K ⊔ 𝔪 ^ k) = K := by
  refine le_antisymm ?_ (le_iInf fun k => le_sup_left)
  intro x hx
  have hbot : (⨅ k : ℕ, (𝔪 ^ k • ⊤ : Submodule A (A ⧸ K))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ K) 𝔪 (maximalIdeal.isMaximal A).ne_top
  have hmk : Submodule.Quotient.mk (p := K) x ∈ (⨅ k : ℕ, (𝔪 ^ k • ⊤ : Submodule A (A ⧸ K))) := by
    rw [Submodule.mem_iInf]
    intro k
    have hxk : x ∈ K ⊔ 𝔪 ^ k := (Submodule.mem_iInf _).mp hx k
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxk
    have : Submodule.Quotient.mk (p := K) (a + b) = b • Submodule.Quotient.mk (p := K) (1 : A) := by
      rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero K).mpr ha, zero_add,
        ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  rw [hbot, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmk
  exact hmk

theorem exists_forall_sup_pow_eq (I : ℕ → Ideal A) (hI : Antitone I) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → I n ⊔ 𝔪 ^ N = I n₀ ⊔ 𝔪 ^ N := by
  classical
  by_cases hN : 𝔪 ^ N = ⊤
  · exact ⟨0, fun n _ => by rw [hN, sup_top_eq, sup_top_eq]⟩

  haveI : Nontrivial (A ⧸ 𝔪 ^ N) := Ideal.Quotient.nontrivial_iff.mpr hN
  haveI : IsLocalRing (A ⧸ 𝔪 ^ N) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (𝔪 ^ N)) Ideal.Quotient.mk_surjective
  have hmap : (𝔪).map (Ideal.Quotient.mk (𝔪 ^ N)) = maximalIdeal (A ⧸ 𝔪 ^ N) := by
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk (𝔪 ^ N)) Ideal.Quotient.mk_surjective
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (le_maximalIdeal hN)]
  haveI : IsArtinianRing (A ⧸ 𝔪 ^ N) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal, ← hmap]
    refine ⟨N, ?_⟩
    rw [← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_quotient_self]

  let f : ℕ →o (Ideal (A ⧸ 𝔪 ^ N))ᵒᵈ :=
    { toFun := fun n => OrderDual.toDual ((I n).map (Ideal.Quotient.mk (𝔪 ^ N)))
      monotone' := fun m n hmn => OrderDual.toDual_le_toDual.mpr (Ideal.map_mono (hI hmn)) }
  obtain ⟨n₀, hn₀⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hn₀ n hn
  have h' : (I n₀).map (Ideal.Quotient.mk (𝔪 ^ N)) = (I n).map (Ideal.Quotient.mk (𝔪 ^ N)) :=
    OrderDual.toDual_inj.mp h
  have := congrArg (Ideal.comap (Ideal.Quotient.mk (𝔪 ^ N))) h'
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker] at this
  exact this.symm

end ChevalleyE95

open ChevalleyE95 in

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (I : ℕ → Ideal A) (hI : Antitone I) (hinf : ⨅ n, I n = ⊥) (N : ℕ) :
    ∃ n, I n ≤ IsLocalRing.maximalIdeal A ^ N := by
  classical
  set m : Ideal A := IsLocalRing.maximalIdeal A with hm

  let J : ℕ → Ideal A := fun M => ⨅ n, (I n ⊔ m ^ M)
  have hJpow : ∀ M, m ^ M ≤ J M := fun M => le_iInf fun n => le_sup_right
  have hJstab : ∀ M, ∃ n₀, ∀ n, n₀ ≤ n → J M = I n ⊔ m ^ M := by
    intro M
    obtain ⟨n₀, hn₀⟩ := exists_forall_sup_pow_eq I hI M
    refine ⟨n₀, fun n hn => le_antisymm (iInf_le _ n) (le_iInf fun k => ?_)⟩
    rw [hn₀ n hn]
    rcases le_total n₀ k with hk | hk
    · rw [← hn₀ k hk]
    · exact sup_le_sup_right (hI hk) _
  have hJanti : Antitone J := by
    intro M M' hMM'
    exact iInf_mono fun n => sup_le_sup_left (Ideal.pow_le_pow_right hMM') _
  have hJsucc : ∀ M, J (M + 1) ⊔ m ^ M = J M := by
    intro M
    obtain ⟨n₁, hn₁⟩ := hJstab M
    obtain ⟨n₂, hn₂⟩ := hJstab (M + 1)
    rw [hn₁ (max n₁ n₂) (le_max_left _ _), hn₂ (max n₁ n₂) (le_max_right _ _), sup_assoc,
      show m ^ (M + 1) ⊔ m ^ M = m ^ M from sup_eq_right.mpr (Ideal.pow_le_pow_right (Nat.le_succ M))]
  have hJinf : ∀ x : A, (∀ M, x ∈ J M) → x = 0 := by
    intro x hx
    have hxI : ∀ n, x ∈ I n := by
      intro n
      rw [← iInf_sup_pow_eq (I n)]
      rw [Submodule.mem_iInf]
      intro k
      exact (Submodule.mem_iInf _).mp (hx k) n
    have : x ∈ (⨅ n, I n) := (Submodule.mem_iInf _).mpr hxI
    rwa [hinf, Submodule.mem_bot] at this

  suffices hmain : J N ≤ m ^ N by
    obtain ⟨n₀, hn₀⟩ := hJstab N
    exact ⟨n₀, le_sup_left.trans ((hn₀ n₀ le_rfl).symm.le.trans hmain)⟩
  intro x hx

  have step : ∀ (k : ℕ) (a : A), a ∈ J (N + k) → ∃ b : A, b ∈ J (N + k + 1) ∧ a - b ∈ m ^ (N + k) := by
    intro k a ha
    rw [← hJsucc (N + k)] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
    exact ⟨b, hb, by rwa [add_sub_cancel_left]⟩
  let s : ∀ k : ℕ, {a : A // a ∈ J (N + k)} := fun k =>
    Nat.rec (motive := fun k => {a : A // a ∈ J (N + k)}) ⟨x, hx⟩
      (fun k a => ⟨Classical.choose (step k a.1 a.2), (Classical.choose_spec (step k a.1 a.2)).1⟩) k
  have hs0 : (s 0 : A) = x := rfl
  have hs_succ : ∀ k, (s k : A) - s (k + 1) ∈ m ^ (N + k) := fun k =>
    (Classical.choose_spec (step k (s k).1 (s k).2)).2
  have hs_tel' : ∀ k d : ℕ, (s k : A) - s (k + d) ∈ m ^ (N + k) := by
    intro k d
    induction d with
    | zero => rw [add_zero, sub_self]; exact Ideal.zero_mem _
    | succ d ih =>
      change (s k : A) - s (k + d + 1) ∈ m ^ (N + k)
      have : (s k : A) - s (k + d + 1) = ((s k : A) - s (k + d)) + ((s (k + d) : A) - s (k + d + 1)) := by
        ring
      rw [this]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right (by omega) (hs_succ (k + d)))
  have hs_tel : ∀ k k', k ≤ k' → (s k : A) - s k' ∈ m ^ (N + k) := by
    intro k k' hkk'
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk'
    exact hs_tel' k d

  have hf : ∀ {k k' : ℕ}, k ≤ k' → (s k : A) ≡ s k' [SMOD (m ^ k • ⊤ : Submodule A A)] := by
    intro k k' hkk'
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_add_left k N) (hs_tel k k' hkk')
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := m) (M := A)) hf
  have hL' : ∀ k, (s k : A) - L ∈ m ^ k := by
    intro k
    have := hL k
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this

  have hLJ : ∀ M, L ∈ J M := by
    intro M
    refine hJanti (Nat.le_add_left M N) ?_
    rw [← iInf_sup_pow_eq (J (N + M)), Submodule.mem_iInf]
    intro k
    have h1 : (s (max M k) : A) ∈ J (N + M) := hJanti (by omega) (s (max M k)).2
    have h2 : L - s (max M k) ∈ m ^ k := by
      rw [← neg_sub]
      exact Submodule.neg_mem _ (Ideal.pow_le_pow_right (le_max_right M k) (hL' (max M k)))
    have : L = s (max M k) + (L - s (max M k)) := by ring
    rw [this]
    exact Submodule.add_mem_sup h1 h2
  have hL0 : L = 0 := hJinf L hLJ
  have hxL : x - L ∈ m ^ N := by
    have h1 : (s 0 : A) - s N ∈ m ^ N := by simpa using hs_tel 0 N (Nat.zero_le N)
    have h2 : (s N : A) - L ∈ m ^ N := hL' N
    have : x - L = ((s 0 : A) - s N) + ((s N : A) - L) := by rw [hs0]; ring
    rw [this]
    exact Ideal.add_mem _ h1 h2
  rwa [hL0, sub_zero] at hxL

end S_IsLocalRing_exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete
end P2MW
export P2MW.S_IsLocalRing_exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete (solution)
