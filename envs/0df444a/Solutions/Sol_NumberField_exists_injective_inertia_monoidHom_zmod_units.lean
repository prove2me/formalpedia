-- Prove2me | solution 1 for NumberField.exists_injective_inertia_monoidHom_zmod_units
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-07T00:50:19.653327+00:00
-- url     : https://prove2.me/submissions/87f0bbac-8c56-4492-ae90-8dab2189e10c

import Mathlib
open NumberField

namespace KWA

variable {K : Type*} [Field K] [NumberField K]

theorem al_smul_mem_pow (Q : Ideal (𝓞 K)) {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ Q.inertia (K ≃ₐ[ℚ] K)) :
    ∀ (n : ℕ) {x : 𝓞 K}, x ∈ Q ^ n → σ • x ∈ Q ^ n := by
  have h1 : ∀ x ∈ Q, σ • x ∈ Q := fun x hx => by
    simpa using Q.add_mem (AddSubgroup.mem_inertia.1 hσ x) hx
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [smul_mul']; exact Ideal.mul_mem_mul (ih ha) (h1 b hb)
    · rw [smul_add]; exact Ideal.add_mem _ ha hb

theorem al_cancel (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) {π x : 𝓞 K} (hπ2 : π ∉ Q ^ 2)
    (h : x * π ∈ Q ^ 2) : x ∈ Q := by
  have := Ideal.IsPrime.isMaximal (inferInstance : Q.IsPrime) hQ
  exact (Ideal.IsMaximal.mul_mem_pow Q h).resolve_right hπ2

/-- A uniformizer of `Q`: an element of `Q \ Q ^ 2`; then `Q = (π) + Q ^ 2`. -/
theorem exists_uniformizer (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ π ∈ Q, π ∉ Q ^ 2 ∧ Q = Ideal.span {π} ⊔ Q ^ 2 := by
  have hQt : Q ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q hQ hQt 1
  rw [pow_one] at hπ1
  have hπ2' : π ∉ Q ^ 2 := hπ2
  refine ⟨π, hπ1, hπ2', ?_⟩
  have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := Q) (I := Ideal.span {π} ⊔ Q ^ 2) hQ
    (i := 1) ?_ ?_
  · rw [pow_one] at h
    exact h.symm
  · rw [SetLike.lt_iff_le_and_exists]
    exact ⟨le_sup_right, π, Ideal.mem_sup_left (Ideal.mem_span_singleton_self π), hπ2⟩
  · rw [pow_one]
    exact sup_le (Ideal.span_le.2 (by simpa using hπ1)) (Ideal.pow_le_self two_ne_zero)

/-- The scalar lemma: an inertia element acts on `Q / Q ^ 2` by the scalar `a`. -/
theorem smul_sub_mul_mem_sq (Q : Ideal (𝓞 K)) [Q.IsPrime] {π : 𝓞 K} (hπ : π ∈ Q)
    (hQπ : Q = Ideal.span {π} ⊔ Q ^ 2) {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ Q.inertia (K ≃ₐ[ℚ] K))
    {a : 𝓞 K} (ha : σ • π - a * π ∈ Q ^ 2) : ∀ y ∈ Q, σ • y - a * y ∈ Q ^ 2 := by
  intro y hy
  obtain ⟨u, z, hz, rfl⟩ := Ideal.mem_span_singleton_sup.1 (hQπ.le hy)
  have e : σ • (u * π + z) - a * (u * π + z) =
      σ • u * (σ • π - a * π) + (σ • u - u) * (a * π) + (σ • z - a * z) := by
    rw [smul_add, smul_mul']; ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) ?_) ?_
  · rw [pow_two]
    exact Ideal.mul_mem_mul (AddSubgroup.mem_inertia.1 hσ u) (Ideal.mul_mem_left _ _ hπ)
  · exact Ideal.sub_mem _ (al_smul_mem_pow Q hσ 2 hz) (Ideal.mul_mem_left _ _ hz)

/-- The tame character `θ : I → (𝓞 K ⧸ Q)`, `θ σ = a mod Q` where `σ π ≡ a π (mod Q ^ 2)`. -/
theorem exists_char (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) {π : 𝓞 K} (hπ : π ∈ Q)
    (hπ2 : π ∉ Q ^ 2) (hQπ : Q = Ideal.span {π} ⊔ Q ^ 2) :
    ∃ θ : Q.inertia (K ≃ₐ[ℚ] K) →* 𝓞 K ⧸ Q, ∀ σ, θ σ ≠ 0 ∧
      ∃ a : 𝓞 K, Ideal.Quotient.mk Q a = θ σ ∧ (σ : K ≃ₐ[ℚ] K) • π - a * π ∈ Q ^ 2 := by
  have h1 : ∀ x ∈ Q, ∀ σ : Q.inertia (K ≃ₐ[ℚ] K), (σ : K ≃ₐ[ℚ] K) • x ∈ Q := fun x hx σ => by
    simpa using Q.add_mem (AddSubgroup.mem_inertia.1 σ.2 x) hx
  have hex : ∀ σ : Q.inertia (K ≃ₐ[ℚ] K), ∃ a : 𝓞 K, (σ : K ≃ₐ[ℚ] K) • π - a * π ∈ Q ^ 2 := by
    intro σ
    obtain ⟨a, z, hz, hz'⟩ := Ideal.mem_span_singleton_sup.1 (hQπ.le (h1 π hπ σ))
    refine ⟨a, ?_⟩
    rw [← hz']
    simpa using hz
  choose a ha using hex
  refine ⟨{ toFun := fun σ => Ideal.Quotient.mk Q (a σ), map_one' := ?_, map_mul' := ?_ },
    fun σ => ⟨?_, a σ, rfl, ha σ⟩⟩
  · show Ideal.Quotient.mk Q (a 1) = 1
    rw [← map_one (Ideal.Quotient.mk Q)]
    apply Ideal.Quotient.eq.2
    apply al_cancel Q hQ hπ2
    have h := ha 1
    have e : (a 1 - 1) * π =
        -((((1 : Q.inertia (K ≃ₐ[ℚ] K)) : K ≃ₐ[ℚ] K)) • π - a 1 * π) := by
      rw [OneMemClass.coe_one, one_smul]; ring
    rw [e]
    exact (Ideal.neg_mem_iff _).2 h
  · intro σ τ
    show Ideal.Quotient.mk Q (a (σ * τ)) = Ideal.Quotient.mk Q (a σ) * Ideal.Quotient.mk Q (a τ)
    rw [← map_mul]
    apply Ideal.Quotient.eq.2
    apply al_cancel Q hQ hπ2
    have hA := smul_sub_mul_mem_sq Q hπ hQπ σ.2 (ha σ) _ (h1 π hπ τ)
    have hB := Ideal.mul_mem_left (Q ^ 2) (a σ) (ha τ)
    have hC := ha (σ * τ)
    have e : (a (σ * τ) - a σ * a τ) * π =
        (((σ : K ≃ₐ[ℚ] K)) • (((τ : K ≃ₐ[ℚ] K)) • π) - a σ * (((τ : K ≃ₐ[ℚ] K)) • π)) +
          a σ * (((τ : K ≃ₐ[ℚ] K)) • π - a τ * π) -
          ((((σ * τ : Q.inertia (K ≃ₐ[ℚ] K)) : K ≃ₐ[ℚ] K)) • π - a (σ * τ) * π) := by
      rw [Subgroup.coe_mul, mul_smul]; ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hA hB) hC
  · intro h0
    change Ideal.Quotient.mk Q (a σ) = 0 at h0
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0
    apply hπ2
    have hσπ : (σ : K ≃ₐ[ℚ] K) • π ∈ Q ^ 2 := by
      have h2 : a σ * π ∈ Q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul h0 hπ
      simpa using Ideal.add_mem _ (ha σ) h2
    have := al_smul_mem_pow Q (σ⁻¹).2 2 hσπ
    rwa [Subgroup.coe_inv, inv_smul_smul] at this

section be
variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

lemma be_D_add (σ : G) (x y : R) : σ • (x + y) - (x + y) = (σ • x - x) + (σ • y - y) := by
  rw [smul_add]; ring

lemma be_D_mul (σ : G) (x y : R) :
    σ • (x * y) - x * y = σ • x * (σ • y - y) + (σ • x - x) * y := by
  rw [smul_mul']; ring

lemma be_D_mem_mul (σ : G) {I J T : Ideal R} (h : ∀ a ∈ I, ∀ b ∈ J, σ • (a * b) - a * b ∈ T)
    {x : R} (hx : x ∈ I * J) : σ • x - x ∈ T := by
  refine Submodule.mul_induction_on hx h (fun x y hx hy => ?_)
  rw [be_D_add]; exact T.add_mem hx hy

lemma be_D_mem_sq (Q : Ideal R) {σ : G} (hσ : ∀ x : R, σ • x - x ∈ Q) {z : R} (hz : z ∈ Q ^ 2) :
    σ • z - z ∈ Q ^ 2 := by
  rw [pow_two] at hz ⊢
  refine be_D_mem_mul σ (fun a ha b hb => ?_) hz
  rw [be_D_mul]
  have hsa : σ • a ∈ Q := by simpa using Q.add_mem (hσ a) ha
  exact Q.mul_mem_mul hsa (hσ b) |> fun h => Ideal.add_mem _ h (Ideal.mul_mem_mul (hσ a) hb)

lemma be_D_mem_sq_of_mem (Q : Ideal R) {π : R} (hπ : π ∈ Q) (hQπ : Q = Ideal.span {π} ⊔ Q ^ 2)
    {σ : G} (hσ : ∀ x : R, σ • x - x ∈ Q) (h2 : σ • π - π ∈ Q ^ 2) {y : R} (hy : y ∈ Q) :
    σ • y - y ∈ Q ^ 2 := by
  rw [hQπ, Ideal.mem_span_singleton_sup] at hy
  obtain ⟨u, z, hz, rfl⟩ := hy
  rw [be_D_add, be_D_mul]
  have hsu : σ • u * (σ • π - π) ∈ Q ^ 2 := Ideal.mul_mem_left _ _ h2
  have hu : (σ • u - u) * π ∈ Q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul (hσ u) hπ
  exact Ideal.add_mem _ (Ideal.add_mem _ hsu hu) (be_D_mem_sq Q hσ hz)

lemma be_D_mem_pow_succ (Q : Ideal R) {π : R} (hπ : π ∈ Q) (hQπ : Q = Ideal.span {π} ⊔ Q ^ 2)
    {σ : G} (hσ : ∀ x : R, σ • x - x ∈ Q) (h2 : σ • π - π ∈ Q ^ 2) :
    ∀ k : ℕ, ∀ y ∈ Q ^ k, σ • y - y ∈ Q ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro y _; simpa using hσ y
  | succ k ih =>
    intro y hy
    rw [pow_succ] at hy
    refine be_D_mem_mul σ (fun a ha b hb => ?_) hy
    rw [be_D_mul]
    have hsa : σ • a ∈ Q ^ k := by
      have := (Q ^ k).add_mem (Ideal.pow_le_pow_right (Nat.le_succ k) (ih a ha)) ha
      simpa using this
    refine Ideal.add_mem _ ?_ ?_
    · have := Ideal.mul_mem_mul hsa (be_D_mem_sq_of_mem Q hπ hQπ hσ h2 hb)
      rw [← pow_add] at this
      exact this
    · have := Ideal.mul_mem_mul (ih a ha) hb
      rw [← pow_succ] at this
      exact this

lemma be_smul_nsmul (σ : G) (m : ℕ) (y : R) : σ • (m • y) = m • (σ • y) := by
  exact smul_comm σ m y

lemma be_D_mem_pow_all (Q : Ideal R) [Q.IsMaximal] {σ : G} {m : ℕ} (hm : σ ^ m = 1)
    (hmQ : (m : R) ∉ Q) (h1 : ∀ k : ℕ, ∀ y ∈ Q ^ k, σ • y - y ∈ Q ^ (k + 1)) :
    ∀ n k : ℕ, ∀ y ∈ Q ^ k, σ • y - y ∈ Q ^ (k + (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    intro k y hy
    have hstab : ∀ j, ∀ x ∈ Q ^ j, σ • x ∈ Q ^ j := fun j x hx => by
      simpa using (Q ^ j).add_mem (Ideal.pow_le_pow_right (Nat.le_succ j) (h1 j x hx)) hx
    have hs : ∀ j : ℕ, (σ ^ j) • y - y ∈ Q ^ (k + (n + 1)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        have e : (σ ^ (j + 1)) • y - y = σ • ((σ ^ j) • y - y) + (σ • y - y) := by
          rw [pow_succ', mul_smul, smul_sub]; abel
        rw [e]
        exact Ideal.add_mem _ (hstab _ _ ihj) (ih k y hy)
    have hfix : σ • (∑ j ∈ Finset.range m, (σ ^ j) • y) = ∑ j ∈ Finset.range m, (σ ^ j) • y := by
      have e1 := Finset.sum_range_succ' (fun j => (σ ^ j) • y) m
      have e2 := Finset.sum_range_succ (fun j => (σ ^ j) • y) m
      simp only [hm, pow_zero, one_smul] at e1 e2
      rw [Finset.smul_sum]
      have : ∑ j ∈ Finset.range m, σ • (σ ^ j) • y = ∑ j ∈ Finset.range m, (σ ^ (j + 1)) • y := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ', mul_smul]
      rw [this]
      exact add_right_cancel (e1.symm.trans e2)
    have hw : (∑ j ∈ Finset.range m, (σ ^ j) • y) - m • y ∈ Q ^ (k + (n + 1)) := by
      have : (∑ j ∈ Finset.range m, (σ ^ j) • y) - m • y
          = ∑ j ∈ Finset.range m, ((σ ^ j) • y - y) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      rw [this]
      exact Ideal.sum_mem _ fun j _ => hs j
    have hDw := ih (k + (n + 1)) _ hw
    rw [smul_sub, hfix, be_smul_nsmul] at hDw
    have e3 : (∑ j ∈ Finset.range m, (σ ^ j) • y) - m • (σ • y) -
        ((∑ j ∈ Finset.range m, (σ ^ j) • y) - m • y) = -((m : R) * (σ • y - y)) := by
      rw [nsmul_eq_mul, nsmul_eq_mul]; ring
    rw [e3, neg_mem_iff] at hDw
    have hle : Q ^ (k + (n + 1) + (n + 1)) ≤ Q ^ (k + (n + 1 + 1)) :=
      Ideal.pow_le_pow_right (by omega)
    rcases Ideal.IsMaximal.mul_mem_pow Q (hle hDw) with h | h
    · exact absurd h hmQ
    · exact h

end be

set_option linter.unusedVariables false in
/-- An inertia element of order prime to `Q` that fixes `π` modulo `Q ^ 2` is trivial. -/
theorem eq_one_of_smul_sub_mem_sq (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) {π : 𝓞 K}
    (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2) (hQπ : Q = Ideal.span {π} ⊔ Q ^ 2) {σ : K ≃ₐ[ℚ] K}
    (hσ : σ ∈ Q.inertia (K ≃ₐ[ℚ] K)) {m : ℕ} (hm : σ ^ m = 1) (hmQ : (m : 𝓞 K) ∉ Q)
    (h2 : σ • π - π ∈ Q ^ 2) : σ = 1 := by
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
  have hσ' : ∀ x : 𝓞 K, σ • x - x ∈ Q := fun x => hσ x
  have hall := be_D_mem_pow_all Q hm hmQ (be_D_mem_pow_succ Q hπ hQπ hσ' h2)
  have hfix : ∀ x : 𝓞 K, σ • x = x := by
    intro x
    have hmem : σ • x - x ∈ ⨅ i, Q ^ i := by
      refine Ideal.mem_iInf.2 fun i => ?_
      cases i with
      | zero => simp
      | succ n => simpa using hall n 0 x (by simp)
    rw [Ideal.iInf_pow_eq_bot_of_isDomain Q (Ideal.IsPrime.ne_top inferInstance), Ideal.mem_bot,
      sub_eq_zero] at hmem
    exact hmem
  have key : ∀ c : 𝓞 K, σ (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K c := by
    intro c
    have : algebraMap (𝓞 K) K (σ • c) = σ (algebraMap (𝓞 K) K c) := rfl
    rw [← this, hfix c]
  apply AlgEquiv.ext
  intro x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  rw [map_div₀, key, key, AlgEquiv.one_apply]


open scoped Pointwise in
theorem ga_smul_sq_eq (Q : Ideal (𝓞 K)) {φ : K ≃ₐ[ℚ] K} (h : φ • Q = Q) :
    φ • (Q ^ 2) = Q ^ 2 := by
  rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, h]

set_option linter.unusedVariables false in
open scoped Pointwise in
/-- The scalar of an inertia element is fixed by Frobenius: `a ^ q ≡ a (mod Q)`. -/
theorem pow_sub_mem [IsAbelianGalois ℚ K] (q : ℕ) (hq : q.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] {π : 𝓞 K} (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2)
    {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ Q.inertia (K ≃ₐ[ℚ] K)) {a : 𝓞 K} (ha : σ • π - a * π ∈ Q ^ 2)
    (hA : ∀ y ∈ Q, σ • y - a * y ∈ Q ^ 2) : a ^ q - a ∈ Q := by
  have hq0 : Ideal.span {(q : ℤ)} ≠ ⊥ := by simp [hq.ne_zero]
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 Q
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) Q
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = q := by
    rw [← Ideal.over_def Q (Ideal.span {(q : ℤ)}), Int.card_ideal_quot]
  have hφ' : ∀ x, φ • x - x ^ q ∈ Q := by
    intro x
    have := hφ x
    rw [hcard] at this
    exact this
  have hstab : φ • Q = Q := MulAction.mem_stabilizer_iff.1 hφ.mem_stabilizer
  have hstab2 := ga_smul_sq_eq Q hstab
  have hsq : ∀ x ∈ Q ^ 2, φ • x ∈ Q ^ 2 := fun x hx => by
    rw [← hstab2]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  have hφπ : φ • π ∉ Q ^ 2 := fun h => by
    rw [← hstab2, Ideal.smul_mem_pointwise_smul_iff] at h
    exact hπ2 h
  have hφπQ : φ • π ∈ Q := by
    rw [← hstab]; exact Ideal.smul_mem_pointwise_smul _ _ _ hπ
  have h1 := hsq _ ha
  have h2 := hA _ hφπQ
  have hcomm : φ • (σ • π) = σ • (φ • π) := by
    rw [← mul_smul, ← mul_smul, mul_comm' φ σ]
  have h3 : (φ • a - a) * (φ • π) ∈ Q ^ 2 := by
    have e : (φ • a - a) * (φ • π) = (σ • (φ • π) - a * (φ • π)) - φ • (σ • π - a * π) := by
      rw [smul_sub, smul_mul', hcomm]; ring
    rw [e]
    exact sub_mem h2 h1
  have h4 : φ • a - a ∈ Q := by
    rcases Ideal.IsMaximal.mul_mem_pow Q h3 with h | h
    · exact h
    · exact absurd h hφπ
  have e : a ^ q - a = -(φ • a - a ^ q) + (φ • a - a) := by ring
  rw [e]
  exact add_mem (neg_mem (hφ' a)) h4

/-- A character into the residue field with values in the prime field lifts to `(ZMod q)ˣ`. -/
theorem exists_monoidHom_zmod_units (q : ℕ) (hq : q.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] (θ : Q.inertia (K ≃ₐ[ℚ] K) →* 𝓞 K ⧸ Q)
    (h0 : ∀ σ, θ σ ≠ 0) (hpow : ∀ σ, θ σ ^ q = θ σ) :
    ∃ f : Q.inertia (K ≃ₐ[ℚ] K) →* (ZMod q)ˣ, ∀ σ, f σ = 1 → θ σ = 1 := by
  have := Fact.mk hq
  have hq0 : Ideal.span {(q : ℤ)} ≠ ⊥ := by simp [hq.ne_zero]
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 Q
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
  let := Ideal.Quotient.field Q
  have hqQ : (q : 𝓞 K) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q (Ideal.span {(q : ℤ)}) (q : ℤ)).1
      (Ideal.mem_span_singleton_self _)
    simpa using this
  have : CharP (𝓞 K ⧸ Q) q := by
    rw [CharP.charP_iff_prime_eq_zero hq, ← map_natCast (Ideal.Quotient.mk Q),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hqQ
  set ι := ZMod.castHom (dvd_refl q) (𝓞 K ⧸ Q) with hι
  have hinj : Function.Injective ι := ZMod.castHom_injective _
  have hex : ∀ σ, ∃ c : ZMod q, ι c = θ σ := fun σ => by
    have hmem : θ σ ∈ (⊥ : Subfield (𝓞 K ⧸ Q)) :=
      (Subfield.mem_bot_iff_pow_eq_self (𝓞 K ⧸ Q) q).2 (hpow σ)
    rw [← ZMod.fieldRange_castHom_eq_bot q] at hmem
    exact RingHom.mem_fieldRange.1 hmem
  choose c hc using hex
  have hc0 : ∀ σ, c σ ≠ 0 := fun σ h => h0 σ (by rw [← hc σ, h, map_zero])
  refine ⟨MonoidHom.mk' (fun σ => Units.mk0 (c σ) (hc0 σ)) (fun σ τ => ?_), fun σ hσ => ?_⟩
  · ext
    simp only [Units.val_mk0, Units.val_mul]
    apply hinj
    rw [map_mul, hc, hc, hc, map_mul]
  · have h1 : c σ = 1 := by
      have := congrArg Units.val hσ
      simpa using this
    rw [← hc σ, h1, map_one]

end KWA

theorem solution (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] (q : ℕ) (hq : q.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] (h : ¬ q ∣ Nat.card (Q.inertia (K ≃ₐ[ℚ] K))) :
    ∃ f : Q.inertia (K ≃ₐ[ℚ] K) →* (ZMod q)ˣ, Function.Injective f := by
  have := Fact.mk hq
  have hq0 : Ideal.span {(q : ℤ)} ≠ ⊥ := by simp [hq.ne_zero]
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 Q
  obtain ⟨π, hπ, hπ2, hQπ⟩ := KWA.exists_uniformizer Q hQ
  obtain ⟨θ, hθ⟩ := KWA.exists_char Q hQ hπ hπ2 hQπ
  have hpow : ∀ σ, θ σ ^ q = θ σ := by
    intro σ
    obtain ⟨-, a, ha1, ha2⟩ := hθ σ
    have hA := KWA.smul_sub_mul_mem_sq Q hπ hQπ σ.2 ha2
    have hq' := KWA.pow_sub_mem q hq Q hπ hπ2 σ.2 ha2 hA
    rw [← ha1, ← map_pow]
    exact Ideal.Quotient.eq.2 hq'
  obtain ⟨f, hf⟩ := KWA.exists_monoidHom_zmod_units q hq Q θ (fun σ => (hθ σ).1) hpow
  refine ⟨f, (injective_iff_map_eq_one f).2 fun σ hσ1 => ?_⟩
  have hθ1 := hf σ hσ1
  obtain ⟨-, a, ha1, ha2⟩ := hθ σ
  have ha3 : a - 1 ∈ Q := Ideal.Quotient.eq.1 (by rw [ha1, hθ1, map_one])
  have h2 : (σ : K ≃ₐ[ℚ] K) • π - π ∈ Q ^ 2 := by
    have e : (σ : K ≃ₐ[ℚ] K) • π - π = ((σ : K ≃ₐ[ℚ] K) • π - a * π) + (a - 1) * π := by ring
    rw [e, pow_two]
    exact Ideal.add_mem _ (pow_two Q ▸ ha2) (Ideal.mul_mem_mul ha3 hπ)
  have hm : (σ : K ≃ₐ[ℚ] K) ^ Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) = 1 := by
    rw [← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
  have hmQ : ((Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) : ℕ) : 𝓞 K) ∉ Q := by
    intro hmem
    apply h
    have h1 := (Ideal.mem_of_liesOver Q (Ideal.span {(q : ℤ)})
      (Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) : ℤ)).2 (by simpa using hmem)
    rw [Ideal.mem_span_singleton] at h1
    exact_mod_cast h1
  exact Subtype.ext (KWA.eq_one_of_smul_sub_mem_sq Q hQ hπ hπ2 hQπ σ.2 hm hmQ h2)
