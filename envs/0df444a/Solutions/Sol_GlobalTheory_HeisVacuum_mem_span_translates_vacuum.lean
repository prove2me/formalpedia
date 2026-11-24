-- Prove2me | solution 1 for GlobalTheory.HeisVacuum.mem_span_translates_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:00.193719+00:00
-- url     : https://prove2.me/submissions/84bd528a-5d64-4c38-b6e4-eabe94823588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanHeisenbergTranslatesOfVacuum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.HeisVacuum
namespace GlobalTheory.HeisVacuum
theorem _root_.solution (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M]
    (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (h0 : ∀ v, ρ 0 v = v)
    (hρ : ∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1)
    (hdiv : ∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x)
    (hfin : ∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u)
    (he : e ≠ 0) (hε : ∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) (h2 : ∀ u ∈ Λ, ρ (2 • u) e = e)
    (hvac : ∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e)
    (v : M) (hv : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) :
    v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  classical
  obtain ⟨N, hN, hv⟩ := hv
  have hsym : ∀ x y, β x y * β y x = 1 := by
    intro x y
    have := hd (x + y)
    rw [hl, hr, hr, hd, hd] at this
    simpa using this
  have hne : ∀ x y, β x y ≠ 0 := fun x y => left_ne_zero_of_mul_eq_one (hsym x y)
  have hz1 : ∀ y, β 0 y = 1 := by
    intro y
    have := hl 0 0 y
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne 0 y)).1 this.symm
  have hz2 : ∀ y, β y 0 = 1 := by
    intro y
    have := hsym y 0
    rwa [hz1, mul_one] at this
  have hp1 : ∀ (n : ℕ) x y, β (n • x) y = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz1]
    | succ n ih => rw [succ_nsmul, hl, ih, pow_succ]
  have hp2 : ∀ (n : ℕ) x y, β x (n • y) = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz2]
    | succ n ih => rw [succ_nsmul, hr, ih, pow_succ]
  have hcomm : ∀ x y w, ρ x (ρ y w) = β x y ^ 2 • ρ y (ρ x w) := by
    intro x y w
    rw [hρ, hρ, smul_smul, add_comm y x, pow_two, mul_assoc, hsym, mul_one]
  have hinv : ∀ t w, ρ t (ρ (-t) w) = w := by
    intro t w
    have := hr t t (-t)
    rw [add_neg_cancel, hz2, hd, one_mul] at this
    rw [hρ, add_neg_cancel, h0, ← this, one_smul]
  choose! ε hε using hε
  have huniq : ∀ u ∈ Λ, ∀ c : ℂ, ρ u e = c • e → c = ε u := by
    intro u hu c hc
    rw [hε u hu] at hc
    exact (smul_left_injective ℂ he hc).symm
  have hεne : ∀ u ∈ Λ, ε u ≠ 0 := by
    intro u hu h
    have := hinv (-u) e
    rw [neg_neg, hε u hu, h, zero_smul, map_zero] at this
    exact he this.symm
  have hεmul : ∀ u ∈ Λ, ∀ u' ∈ Λ, ε u * ε u' = β u u' * ε (u + u') := by
    intro u hu u' hu'
    have := hρ u u' e
    rw [hε u' hu', map_smul, hε u hu, hε _ (Λ.add_mem hu hu'), smul_smul, smul_smul, mul_comm] at this
    exact smul_left_injective ℂ he this
  let A : Λ → M → M := fun u w => (ε u)⁻¹ • ρ u w
  have hA : ∀ (u u' : Λ) w, A u (A u' w) = A (u + u') w := by
    intro u u' w
    simp only [A, map_smul, hρ, smul_smul, AddSubgroup.coe_add]
    congr 1
    have h1 := hεmul u u.2 u' u'.2
    have h3 := hεne u u.2
    have h4 := hεne u' u'.2
    have h5 := hεne _ (Λ.add_mem u.2 u'.2)
    field_simp
    rw [h1, mul_comm]
  have hA0 : ∀ w, A 0 w = w := by
    intro w
    have : (1 : ℂ) = ε 0 := huniq 0 Λ.zero_mem 1 (by rw [h0, one_smul])
    simp [A, h0, ← this]
  set K : ℕ := 2 * N with hK
  have hKpos : 0 < K := by omega
  have hεK : ∀ u ∈ Λ, ε (K • u) = 1 := by
    intro u hu
    refine (huniq _ (Λ.nsmul_mem hu K) 1 ?_).symm
    rw [one_smul, hK, mul_comm, mul_nsmul]
    exact h2 _ (Λ.nsmul_mem hu N)
  have hvK : ∀ u ∈ Λ, ρ (K • u) v = v := by
    intro u hu
    rw [hK, mul_nsmul]
    exact hv _ (Λ.nsmul_mem hu 2)
  let H : AddSubgroup Λ := (nsmulAddMonoidHom K : Λ →+ Λ).range
  have hQ : Finite (Λ ⧸ H) := by
    obtain ⟨R, hR, hR'⟩ := hfin K hKpos
    have : Finite {x : Λ // (x : X) ∈ R} := by
      have : Finite R := hR
      exact Finite.of_injective (fun x : {x : Λ // (x : X) ∈ R} => (⟨x.1, x.2⟩ : R))
        (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : X)) h)))
    refine Finite.of_surjective (fun x : {x : Λ // (x : X) ∈ R} => (QuotientAddGroup.mk x.1 : Λ ⧸ H)) ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, u, hu, htu⟩ := hR' t t.2
    have hrΛ : r ∈ Λ := by
      have : r = t - K • u := by rw [htu]; abel
      rw [this]
      exact Λ.sub_mem t.2 (Λ.nsmul_mem hu K)
    refine ⟨⟨⟨r, hrΛ⟩, hr⟩, ?_⟩
    refine QuotientAddGroup.eq.2 ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    simp [htu]
  have := Fintype.ofFinite (Λ ⧸ H)
  have hwell : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∀ x y : Λ,
      (QuotientAddGroup.mk x : Λ ⧸ H) = QuotientAddGroup.mk y → A x w = A y w := by
    intro w hw x y hxy
    obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 hxy
    have h1 : y = x + K • u := by
      have : K • u = -x + y := hu
      rw [this]; abel
    have h3 : A (K • u) w = w := by
      simp only [A, AddSubgroup.coe_nsmul, hεK u u.2, hw u u.2, inv_one, one_smul]
    rw [h1, ← hA, h3]
  have hAsum : ∀ (u : Λ) (f : Λ ⧸ H → M), A u (∑ q, f q) = ∑ q, A u (f q) := by
    intro u f
    simp only [A, map_sum, Finset.smul_sum]
  have hP : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∃ c : ℂ, (∑ q : Λ ⧸ H, A q.out w) = c • e := by
    intro w hw
    apply hvac
    intro u hu c hc
    rw [huniq u hu c hc]
    have h1 : A ⟨u, hu⟩ (∑ q : Λ ⧸ H, A q.out w) = ∑ q : Λ ⧸ H, A q.out w := by
      rw [hAsum]
      refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk ⟨u, hu⟩ : Λ ⧸ H)) _ _ ?_
      intro q
      rw [hA]
      apply hwell w hw
      simp
    conv_rhs => rw [← h1]
    simp only [A, smul_smul, mul_inv_cancel₀ (hεne u hu), one_smul]
  let Tg : AddSubgroup X := Λ.comap (nsmulAddMonoidHom K : X →+ X)
  have hTg : ∀ t, t ∈ Tg ↔ K • t ∈ Λ := fun t => Iff.rfl
  let S := Submodule.span ℂ (Set.range fun x => ρ x e)
  have hmem : ∀ t ∈ Tg, (∑ q : Λ ⧸ H, β t (q.out : Λ) ^ 2 • A q.out v) ∈ S := by
    intro t ht
    obtain ⟨c, hc⟩ := hP (ρ (-t) v) (by
      intro u hu
      rw [hcomm, hvK u hu, hp1, ← hp2, (hΛ u).1 hu _ ((hTg _).1 (Tg.neg_mem ht)), one_smul])
    have h1 := congrArg (ρ t) hc
    rw [map_sum, map_smul] at h1
    have h3 : c • ρ t e ∈ S := S.smul_mem c (Submodule.subset_span ⟨t, rfl⟩)
    rw [← h1] at h3
    convert h3 using 2 with q
    simp only [A, map_smul]
    rw [hcomm t, hinv, smul_comm]
  let χ : Λ ⧸ H → (Multiplicative Tg →* ℂ) := fun q =>
    { toFun := fun t => β (t.toAdd : Tg) (q.out : Λ) ^ 2
      map_one' := by simp [hz1]
      map_mul' := by intro a b; simp [hl, mul_pow] }
  have hχ : Function.Injective χ := by
    intro q q' h
    have h1 : ∀ t ∈ Tg, β t (q.out : Λ) ^ 2 = β t (q'.out : Λ) ^ 2 := fun t ht =>
      DFunLike.congr_fun h (Multiplicative.ofAdd ⟨t, ht⟩)
    obtain ⟨y, hy⟩ := hdiv K hKpos (-((q.out : Λ) : X) + (q'.out : Λ))
    have hyΛ : y ∈ Λ := by
      rw [hΛ]
      intro a ha
      obtain ⟨t, rfl⟩ := hdiv K hKpos a
      have h3 := h1 t ha
      have h4 : ((q'.out : Λ) : X) = (q.out : Λ) + K • y := by rw [hy]; abel
      rw [h4, hr, mul_pow, hp2, ← hp1 K] at h3
      have h5 : β (K • t) y ^ 2 = 1 :=
        (mul_eq_left₀ (pow_ne_zero 2 (hne _ _))).1 h3.symm
      have h6 := congrArg (· ^ 2) (hsym y (K • t))
      simpa [mul_pow, h5] using h6
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    exact QuotientAddGroup.eq.2 ⟨⟨y, hyΛ⟩, Subtype.ext (by simpa using hy)⟩
  have hli : LinearIndependent ℂ (fun q => (χ q : Multiplicative Tg → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative Tg) ℂ).comp χ hχ
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have h1 := Fintype.linearIndependent_iff.1 hli (fun q => φ (S.mkQ (A q.out v))) (by
    funext t
    have h3 := (Submodule.Quotient.mk_eq_zero S).2 (hmem _ (t.toAdd).2)
    have h4 := congrArg φ h3
    rw [← Submodule.mkQ_apply, map_sum, map_sum, map_zero] at h4
    simp only [map_smul, smul_eq_mul] at h4
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h4]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _) 0
  have h3 : A (0 : Λ ⧸ H).out v = v := by
    rw [hwell v hvK _ 0 (by simp), hA0]
  simpa [h3] using h1
end GlobalTheory.HeisVacuum
