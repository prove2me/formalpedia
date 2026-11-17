-- Prove2me | solution 1 for LatticePrepro.ObliviousPCP.lt_hammingNorm_stackMap_of_solution
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:12:56.260631+00:00
-- url     : https://prove2.me/submissions/897f7a3b-28d5-4119-a18a-e75a9e06c775

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code
import Theorems.Thm_LatticePrepro_mul_le_sum_of_sum_prod_inv_le

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ObliviousPCP end LatticePrepro.ObliviousPCP

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X)

variable {P} in
lemma View.eval_eq {r : P.Rand} (w : P.View r) : P.eval r w.pred w.ans = true := w.2.1

variable {P} in
lemma View.ans_eq {r : P.Rand} (w : P.View r) {j j' : Fin P.q}
    (h : P.query r j = P.query r j') : w.ans j = w.ans j' := w.2.2 j j' h

/-- The number of random strings is `2^ρ`. -/
lemma card_rand : Fintype.card P.Rand = 2 ^ P.ρ := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end ObliviousPCP

end LatticePrepro

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) (F : Type) [Field F]

lemma constraintMap_apply (v : P.Views → F) (r : P.Rand) (V : P.Pred r) :
    P.constraintMap F v ⟨r, V⟩ = ∑ w : P.View r, if w.pred = V then v ⟨r, w⟩ else 0 := rfl

lemma constraintRhs_apply (x : X) (r : P.Rand) (V : P.Pred r) :
    P.constraintRhs F x ⟨r, V⟩ = if V = P.verifier x r then 1 else 0 := rfl

lemma restrict_apply (u : Fin P.ℓ) (a : P.Alphabet) (v : P.Views → F) (i : P.Views) :
    P.restrict F u a v i = if P.Hits u a i then v i else 0 := rfl

variable {F} {B : ℕ}

end ObliviousPCP

end LatticePrepro

namespace LatticePrepro

/-- The Hamming weight of a vector on a product type is the sum of the weights of its slices. -/
lemma hammingNorm_prod {α β γ : Type*} [Fintype α] [Fintype β] [Zero γ] [DecidableEq γ]
    (f : α × β → γ) : hammingNorm f = ∑ a, hammingNorm fun b => f (a, b) := by
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_prod_type]

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

/-- The weight of `G₁ · v` (equation (29)), with the copies indexed by the queries `(r, j)`. -/
lemma hammingNorm_stackMap (E : (P.Views → F) →ₗ[F] (Fin B → F)) (v : P.Views → F) :
    hammingNorm (P.stackMap E v) =
      ∑ r : P.Rand, ∑ j : Fin P.q, ∑ a : P.Alphabet,
        hammingNorm (E (P.restrict F (P.query r j) a v)) := by
  rw [hammingNorm_prod]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hammingNorm_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hammingNorm_prod]
  rfl

/-- The heart of the soundness proof: for `x ∉ Lang`, every solution of `G₀ · v = b_x` has
weight `W(v) > g · Y`. -/
private theorem lt_hammingNorm_stackMap_of_solution {Lang : Set X} {ε δ : ℝ}
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) {v : P.Views → F}
    (hv : P.constraintMap F v = P.constraintRhs F x) :
    g * P.radius B < hammingNorm (P.stackMap E v) := by
  classical
  -- For every random string, a view with predicate `V_{x,r}` in the support of `v`.
  have hview : ∀ r : P.Rand, ∃ w : P.View r, w.pred = P.verifier x r ∧ v ⟨r, w⟩ ≠ 0 := by
    intro r
    have h1 := congrFun hv ⟨r, P.verifier x r⟩
    rw [constraintMap_apply, constraintRhs_apply, if_pos rfl] at h1
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1.trans_ne one_ne_zero)
    by_cases hp : w.pred = P.verifier x r
    · exact ⟨w, hp, by rwa [if_pos hp] at hw⟩
    · rw [if_neg hp] at hw
      exact absurd rfl hw
  choose w hwp hwv using hview
  -- The lists `Λ_u`, which contain the answers of these views.
  set Λ : Fin P.ℓ → Finset P.Alphabet :=
    fun u => Finset.univ.filter fun a => P.restrict F u a v ≠ 0 with hΛ
  have hΛmem : ∀ u a, a ∈ Λ u ↔ P.restrict F u a v ≠ 0 := fun u a => by
    simp only [hΛ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem : ∀ r j, (w r).ans j ∈ Λ (P.query r j) := by
    intro r j
    rw [hΛmem]
    intro h0
    have h1 := congrFun h0 ⟨r, w r⟩
    have hit : P.Hits (P.query r j) ((w r).ans j) ⟨r, w r⟩ := ⟨j, rfl, rfl⟩
    rw [restrict_apply, if_pos hit] at h1
    exact hwv r h1
  -- Proofs with entries in the lists (a fixed symbol at the locations with an empty list).
  let r₀ : P.Rand := fun _ => false
  let a₀ : P.Alphabet := (w r₀).ans ⟨0, P.q_pos⟩
  set L : Fin P.ℓ → Finset P.Alphabet :=
    fun u => if (Λ u).Nonempty then Λ u else {a₀} with hL
  have hLq : ∀ r j, L (P.query r j) = Λ (P.query r j) := fun r j => by
    simp only [hL]
    rw [if_pos ⟨_, hmem r j⟩]
  have hLne : ∀ u, (L u).Nonempty := fun u => by
    simp only [hL]
    split_ifs with h
    · exact h
    · exact Finset.singleton_nonempty _
  set S : Finset P.Proof := Fintype.piFinset L with hS
  have hSpos : 0 < S.card := by
    rw [hS, Fintype.card_piFinset]
    exact Finset.prod_pos fun u _ => (hLne u).card_pos
  -- For every random string, at least a `∏_j |Λ_{u_{r,j}}|⁻¹` fraction of these proofs is
  -- accepted: overwriting a proof with the answers of the view `w r` gives an accepted proof.
  have hcount : ∀ r : P.Rand, S.card ≤
      (S.filter fun π => P.Accepts x r π).card * ∏ j, (Λ (P.query r j)).card := by
    intro r
    let ov : P.Proof → P.Proof :=
      fun π u => if h : ∃ j, P.query r j = u then (w r).ans h.choose else π u
    have hov : ∀ π j, ov π (P.query r j) = (w r).ans j := by
      intro π j
      have h : ∃ j', P.query r j' = P.query r j := ⟨j, rfl⟩
      show (if h : ∃ j', P.query r j' = P.query r j then (w r).ans h.choose
        else π (P.query r j)) = (w r).ans j
      rw [dif_pos h]
      exact (w r).ans_eq h.choose_spec
    have hov' : ∀ π u, (¬ ∃ j, P.query r j = u) → ov π u = π u := fun π u h => dif_neg h
    have hinj : Set.InjOn (fun π : P.Proof => (ov π, fun j => π (P.query r j)))
        (S : Set P.Proof) := by
      intro π₁ _ π₂ _ h
      have h1 : ov π₁ = ov π₂ := congrArg Prod.fst h
      have h2 : (fun j => π₁ (P.query r j)) = fun j => π₂ (P.query r j) := congrArg Prod.snd h
      funext u
      by_cases hu : ∃ j, P.query r j = u
      · obtain ⟨j, rfl⟩ := hu
        exact congrFun h2 j
      · rw [← hov' π₁ u hu, ← hov' π₂ u hu, h1]
    have hmaps : ∀ π ∈ S, (fun π : P.Proof => (ov π, fun j => π (P.query r j))) π ∈
        (S.filter fun π => P.Accepts x r π) ×ˢ Fintype.piFinset fun j => Λ (P.query r j) := by
      intro π hπ
      rw [hS, Fintype.mem_piFinset] at hπ
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · show ov π ∈ S
        rw [hS, Fintype.mem_piFinset]
        intro u
        by_cases hu : ∃ j, P.query r j = u
        · obtain ⟨j, rfl⟩ := hu
          rw [hov, hLq]
          exact hmem r j
        · rw [hov' π u hu]
          exact hπ u
      · show P.eval r (P.verifier x r) (fun j => ov π (P.query r j)) = true
        have h1 : (fun j => ov π (P.query r j)) = (w r).ans := funext fun j => hov π j
        rw [h1, ← hwp r]
        exact (w r).eval_eq
      · show (fun j => π (P.query r j)) ∈ Fintype.piFinset fun j => Λ (P.query r j)
        rw [Fintype.mem_piFinset]
        intro j
        rw [← hLq]
        exact hπ _
    calc S.card ≤ ((S.filter fun π => P.Accepts x r π) ×ˢ
          Fintype.piFinset fun j => Λ (P.query r j)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = (S.filter fun π => P.Accepts x r π).card * ∏ j, (Λ (P.query r j)).card := by
          rw [Finset.card_product, Fintype.card_piFinset]
  -- Soundness of the PCP bounds the number of accepted pairs (equation (31), first step).
  set lam : P.Rand → Fin P.q → ℝ := fun r j => ((Λ (P.query r j)).card : ℝ) with hlam
  have hlampos : ∀ r j, 0 < lam r j := fun r j => by
    simp only [hlam]
    exact_mod_cast Finset.card_pos.mpr ⟨_, hmem r j⟩
  have hsum : ∑ r, ∏ j, (lam r j)⁻¹ ≤ ε * 2 ^ P.ρ := by
    have h1 : ∀ r : P.Rand, (S.card : ℝ) * ∏ j, (lam r j)⁻¹ ≤
        ((S.filter fun π => P.Accepts x r π).card : ℝ) := by
      intro r
      have hp : 0 < ∏ j, lam r j := Finset.prod_pos fun j _ => hlampos r j
      rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, div_le_iff₀ hp]
      have h' : ((S.card : ℕ) : ℝ) ≤
          (((S.filter fun π => P.Accepts x r π).card * ∏ j, (Λ (P.query r j)).card : ℕ) : ℝ) :=
        Nat.cast_le.mpr (hcount r)
      rw [Nat.cast_mul, Nat.cast_prod] at h'
      exact h'
    have h2 : (∑ r : P.Rand, ((S.filter fun π => P.Accepts x r π).card : ℝ)) =
        ∑ π ∈ S, ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    have h3 : ∑ π ∈ S, ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ) ≤
        S.card * (ε * 2 ^ P.ρ) := by
      calc ∑ π ∈ S, ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ)
          ≤ ∑ _π ∈ S, ε * 2 ^ P.ρ := Finset.sum_le_sum fun π _ => hs x hx π
        _ = S.card * (ε * 2 ^ P.ρ) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : (S.card : ℝ) * ∑ r, ∏ j, (lam r j)⁻¹ ≤ S.card * (ε * 2 ^ P.ρ) := by
      rw [Finset.mul_sum]
      exact (Finset.sum_le_sum fun r _ => h1 r).trans (h2.le.trans h3)
    exact le_of_mul_le_mul_left h4 (Nat.cast_pos.mpr hSpos)
  -- The total list size is at least `2^ρ · q · ε^{-1/q}` (equation (31)).
  set t : ℝ := ε ^ (-(1 : ℝ) / P.q) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hε _
  have hq0 : (P.q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr P.q_pos.ne'
  have htq : t ^ P.q = ε⁻¹ := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hε.le, div_mul_cancel₀ _ hq0, Real.rpow_neg_one]
  have hcard : (Fintype.card P.Rand : ℝ) = 2 ^ P.ρ := by
    rw [P.card_rand]
    push_cast
    rfl
  have hkey : (2 : ℝ) ^ P.ρ * P.q * t ≤ ∑ r, ∑ j, lam r j := by
    have h1 : (∑ r, ∏ j, (lam r j)⁻¹) * t ^ P.q ≤ Fintype.card P.Rand := by
      rw [htq, hcard]
      calc (∑ r, ∏ j, (lam r j)⁻¹) * ε⁻¹ ≤ ε * 2 ^ P.ρ * ε⁻¹ :=
            mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hε.le)
        _ = 2 ^ P.ρ := by
            field_simp
    have h2 := mul_le_sum_of_sum_prod_inv_le lam hlampos htpos h1
    rwa [hcard] at h2
  -- The encoding has `B ≥ 1` coordinates, since it is injective on a nonzero space.
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with rfl | h
    · exfalso
      have hne := (hΛmem _ _).mp (hmem r₀ ⟨0, P.q_pos⟩)
      exact hne (hE (Subsingleton.elim _ _))
    · exact h
  have hδpos : 0 < δ := by
    by_contra h
    have h1 : δ * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) htpos.le
    have h2 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    linarith
  -- Every symbol of a list contributes weight at least `δ · B` (equation (29)).
  have hweight : δ * B * ∑ r, ∑ j, lam r j ≤ (hammingNorm (P.stackMap E v) : ℝ) := by
    rw [P.hammingNorm_stackMap, Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Nat.cast_sum]
    calc δ * B * lam r j = ∑ _a ∈ Λ (P.query r j), δ * B := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ Λ (P.query r j),
            (hammingNorm (E (P.restrict F (P.query r j) a v)) : ℝ) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hne : P.restrict F (P.query r j) a v ≠ 0 := (hΛmem _ _).mp ha
          exact hδ _ (LinearMap.mem_range.mpr ⟨_, rfl⟩)
            (fun h0 => hne (hE (h0.trans (map_zero E).symm)))
      _ ≤ ∑ a, (hammingNorm (E (P.restrict F (P.query r j) a v)) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => Nat.cast_nonneg _
  have hY : (0 : ℝ) < (P.radius B : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos hB (pow_pos (by norm_num) _)) P.q_pos)
  have hfinal : (g : ℝ) * P.radius B < (hammingNorm (P.stackMap E v) : ℝ) := by
    calc (g : ℝ) * P.radius B < δ * t * P.radius B := mul_lt_mul_of_pos_right hg hY
      _ = δ * B * ((2 : ℝ) ^ P.ρ * P.q * t) := by
          simp only [radius]
          push_cast
          ring
      _ ≤ δ * B * ∑ r, ∑ j, lam r j :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hδpos.le (Nat.cast_nonneg B))
      _ ≤ (hammingNorm (P.stackMap E v) : ℝ) := hweight
  exact_mod_cast hfinal

end ObliviousPCP

end LatticePrepro

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}
theorem solution {Lang : Set X} {ε δ : ℝ}
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) {v : P.Views → F}
    (hv : P.constraintMap F v = P.constraintRhs F x) :
    g * P.radius B < hammingNorm (P.stackMap E v) :=
  @LatticePrepro.ObliviousPCP.lt_hammingNorm_stackMap_of_solution X P F _ _ B Lang ε δ hs hε E hE hδ g hg x hx v hv
