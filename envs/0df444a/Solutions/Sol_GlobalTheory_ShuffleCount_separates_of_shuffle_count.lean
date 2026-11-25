-- Prove2me | solution 1 for GlobalTheory.ShuffleCount.separates_of_shuffle_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:20.935087+00:00
-- url     : https://prove2.me/submissions/98c5d6c7-14a9-4b5f-8248-6b1d64040468

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ShuffleCountLinearIndependentClasses
import Theorems.Thm_GlobalTheory_ShuffleCount_coeff_eq_zero_of_aeval_eq_zero
import Theorems.Thm_GlobalTheory_Lyndon_repr_sum_word
import Theorems.Thm_GlobalTheory_Published_RadfordShufflePolynomial_algebraicIndependent
import Theorems.Thm_GlobalTheory_Published_radfordShufflePolynomial_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory GlobalTheory.ShuffleCount
open MvPolynomial
namespace GlobalTheory.ShuffleCount
theorem _root_.solution : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by
  intro I S A _ _ Ψ M U ℓ φ hinj hU hφ0 hcnt n p c hp hne hc
  classical
  let Rh : List A → (I →₀ ℤ) →+ ℤ := fun w =>
    Finsupp.liftAddHom fun x => AddMonoidHom.mulRight ((M x w).toNat : ℤ)
  have hRs : ∀ w x a, Rh w (Finsupp.single x a) = a * ((M x w).toNat : ℤ) := fun w x a => by
    simp [Rh]
  have hRsum : ∀ w (y : I →₀ ℤ), Rh w y = y.sum fun x a => a * ((M x w).toNat : ℤ) := fun w y => by
    simp [Rh, Finsupp.liftAddHom_apply]
  have K0 : ∀ (y : I →₀ ℤ) (w : List A) (N : ℕ), 0 ≤ y →
      (y.sum fun x a => (a.toNat : ℕ∞) * M x w) = (N : ℕ∞) → Rh w y = N := by
    intro y w N hy hN
    rw [Finsupp.sum] at hN
    have hfin : ∀ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w ≠ ⊤ := by
      intro x hx htop
      have hle : ((y x).toNat : ℕ∞) * M x w ≤ ∑ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w :=
        Finset.single_le_sum (f := fun x => ((y x).toNat : ℕ∞) * M x w) (fun _ _ => zero_le) hx
      rw [hN, htop] at hle
      exact ENat.natCast_ne_top N (top_le_iff.1 hle)
    have h1 := congrArg ENat.toNat hN
    rw [ENat.toNat_sum hfin, ENat.toNat_natCast] at h1
    simp only [ENat.toNat_mul, ENat.toNat_natCast] at h1
    rw [hRsum, Finsupp.sum, ← h1, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_mul, Int.toNat_of_nonneg (Finsupp.le_def.1 hy x)]
  have K1 : ∀ (w : List A) (P : MvPolynomial S ℤ),
      (ShuffleAlgebra.wordBasis ℚ A).repr (aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P)) w =
        ((Rh w (Ψ.symm P) : ℤ) : ℚ) := by
    intro w P
    induction P using MvPolynomial.induction_on' with
    | monomial m r =>
      obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
      have hmr : (MvPolynomial.monomial m r : MvPolynomial S ℤ) = r • MvPolynomial.monomial m 1 := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, ← hs2, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, Lyndon.repr_sum_word, hmr, map_zsmul, map_zsmul, K0 _ w _ hpos (hs1 w),
        smul_eq_mul, smul_eq_mul]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      congr
    | add P Q hP hQ =>
      simp only [map_add, Finsupp.add_apply, hP, hQ, Int.cast_add]
  have K2 : ∀ m : S →₀ ℕ, (∃ Δ ∈ m.support, Δ ∉ U) →
      ∀ x, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0 → ∀ w, M x w = 0 := by
    rintro m ⟨Δ, hΔ, hΔU⟩ x hx w
    obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
    have hprod : (m.prod fun Δ e => φ Δ ^ e) = 0 :=
      Finset.prod_eq_zero hΔ (by show φ Δ ^ m Δ = 0; rw [hφ0 Δ hΔU, zero_pow (Finsupp.mem_support_iff.1 hΔ)])
    have hcount : s.count w = 0 := by
      have h := Lyndon.repr_sum_word ℚ s w
      rw [hs2, hprod, map_zero, Finsupp.zero_apply] at h
      have h'' := Nat.cast_eq_zero.1 h.symm
      convert h''
    have h1 := hs1 w
    rw [hcount, Finsupp.sum, Nat.cast_zero, Finset.sum_eq_zero_iff] at h1
    have h2 := h1 x (Finsupp.mem_support_iff.2 hx)
    rcases mul_eq_zero.1 h2 with h | h
    · exfalso
      have hnn := Finsupp.le_def.1 hpos x
      have h0 : (Ψ.symm (MvPolynomial.monomial m 1) x).toNat = 0 := by exact_mod_cast h
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hnn
      omega
    · exact h
  have hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ) := by
    have hR := Published.radfordShufflePolynomial_holds.algebraicIndependent ℚ A
    have he : Function.Injective
        (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      intro a b hab
      exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
    have hcomp := hR.comp _ he
    have heq : (fun Δ : U => φ Δ) =
        (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word ℚ l.1) ∘
          (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      funext Δ
      exact (hU Δ Δ.2).2
    rw [heq]
    exact hcomp
  have K3 : ∀ k : Fin n → ℤ, (∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0) → ∀ i, k i = 0 := by
    intro k hk i
    by_contra hki
    set y : I →₀ ℤ := ∑ j, Finsupp.single (p j) (k j) with hy
    have hRy : ∀ w, Rh w y = 0 := fun w => by
      rw [hy, map_sum]
      simp only [hRs]
      exact hk w
    set P := Ψ y with hPdef
    have hEv : aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P) = 0 := by
      apply (ShuffleAlgebra.wordBasis ℚ A).repr.injective
      rw [map_zero]
      ext w
      rw [K1, hPdef, AddEquiv.symm_apply_apply, hRy, Int.cast_zero, Finsupp.zero_apply]
    have hcoef : ∀ m : S →₀ ℕ, (∀ Δ ∈ m.support, Δ ∈ U) → P.coeff m = 0 := by
      intro m hm
      have h := coeff_eq_zero_of_aeval_eq_zero U φ hind hφ0 _ hEv m hm
      rw [MvPolynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at h
      exact h
    have hyP : y = ∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1) := by
      have h : y = Ψ.symm P := by rw [hPdef, AddEquiv.symm_apply_apply]
      conv_lhs => rw [h, P.as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_zsmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hyi : y (p i) = k i := by
      rw [hy, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg]
        exact fun h => hji (hp h)
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hne0 : (∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)) (p i) ≠ 0 := by
      rw [← hyP, hyi]
      exact hki
    rw [Finsupp.finsetSum_apply] at hne0
    obtain ⟨m, _, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    rw [Finsupp.smul_apply, smul_eq_mul] at hm0
    have hc0 : P.coeff m ≠ 0 := left_ne_zero_of_mul hm0
    have hx0 : Ψ.symm (MvPolynomial.monomial m 1) (p i) ≠ 0 := right_ne_zero_of_mul hm0
    have hout : ∃ Δ ∈ m.support, Δ ∉ U := by
      by_contra h
      push_neg at h
      exact hc0 (hcoef m h)
    obtain ⟨w, hw⟩ := hne i
    exact hw (K2 m hout (p i) hx0 w)
  have KQ : ∀ q : Fin n → ℚ, (∀ w, ∑ j, q j * ((M (p j) w).toNat : ℚ) = 0) → ∀ i, q i = 0 := by
    intro q hq i
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Fin n)) q
    choose k hk using fun j => RingHom.mem_rangeS.1 (hb j (Finset.mem_univ j))
    have hk' : ∀ j, (k j : ℚ) = ((b : ℤ) : ℚ) * q j := fun j => by
      simpa [Algebra.smul_def] using hk j
    have hkrel : ∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0 := by
      intro w
      have h : ((∑ j, k j * ((M (p j) w).toNat : ℤ) : ℤ) : ℚ) = 0 := by
        push_cast
        simp only [hk', mul_assoc, ← Finset.mul_sum, hq w, mul_zero]
      exact_mod_cast h
    have hki := K3 k hkrel i
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
    have h2 := hk' i
    rw [hki, Int.cast_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left hb0
  intro i
  have hq : ∀ ψ : Module.Dual ℚ ℂ, ∀ j, ψ (c j) = 0 := by
    intro ψ
    apply KQ (fun j => ψ (c j))
    intro w
    have h := congrArg ψ (hc w)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ψ (c j) * _ = ψ (c j * _)
    rw [mul_comm (c j), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (c i)).1 fun ψ => hq ψ i
end GlobalTheory.ShuffleCount
