-- Prove2me | solution 1 for GlobalTheory.TorsionZero.card_zeros_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:18:56.254844+00:00
-- url     : https://prove2.me/submissions/b4179e12-15eb-4cdf-b3f1-3da8287a0ee0

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
import Theorems.Thm_GlobalTheory_TorsionZero_aeval_mul_of_isHomogeneous
import Theorems.Thm_GlobalTheory_TorsionZero_ringKrullDim_cone
import Theorems.Thm_GlobalTheory_TorsionZero_mem_subGrading
import Theorems.Thm_GlobalTheory_TorsionZero_nonempty_gradedAlgebra_subGrading
import Theorems.Thm_GlobalTheory_TorsionZero_map_eq_pow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]
namespace GlobalTheory.TorsionZero
theorem _root_.solution [IsAlgClosed K] [IsDomain R] (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
    (hInt : ∀ (T : Type) [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m : ℕ) (x : Fin m → T), (∀ i, x i ∈ 𝒜 1) → (∃ i, x i ≠ 0) → ∀ (d : ℕ), ∀ s ∈ 𝒜 d, (∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) → IsIntegral (Algebra.adjoin K (Set.range x)) s)
    (hBez : ∀ (T : Type) [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m g N d a : ℕ) (x : Fin m → T) (s : T) (F : Set T), 1 ≤ g → (∀ i, x i ∈ 𝒜 1) → Module.Finite (Algebra.adjoin K (Set.range x)) T → ringKrullDim T = (g + 1 : ℕ) → (∀ e, 1 ≤ e → Module.finrank K (𝒜 e) ≤ (N * e) ^ g) → s ∈ 𝒜 d → s ≠ 0 → (∀ f ∈ F, f ∈ 𝒜 a) → (∃ Φ : Set (T →ₐ[K] K), Φ.Finite ∧ ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) → ∃ ψ ∈ Φ, (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)) → ∀ (n : ℕ) (φ : Fin n → (T →ₐ[K] K)), (∀ j, ∃ i, φ j (x i) ≠ 0) → (∀ j, φ j s = 0 ∧ ∀ f ∈ F, φ j f = 0) → (∀ j j', (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ j' y = c ^ e * φ j y) → j = j') → n ≤ N ^ g * g.factorial * d * a ^ (g - 1))
    {m g N d a : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) (x : Fin m → R) (hx : ∀ j, x j ∈ 𝒜 N)
    (hform : ∀ e, ∀ y ∈ 𝒜 (N * e), ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K),
      G.IsHomogeneous (n + e) ∧ y * x i ^ n = aeval x G)
    {C : Type} [CommRing C] [IsDomain C] [Algebra K C] (r : Fin m → C) (i₀ : Fin m) (hi₀ : r i₀ = 1)
    (hx₀ : x i₀ ≠ 0)
    (hr : Function.Surjective (aeval r : MvPolynomial (Fin m) K →ₐ[K] C))
    (hrel : ∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0))
    (hC : ringKrullDim C = g)
    (hfin : ∀ e, 1 ≤ e → Module.Finite K (𝒜 (N * e)) ∧ Module.finrank K (𝒜 (N * e)) ≤ (N * e) ^ g)
    (s : R) (hs : s ∈ 𝒜 (N * d)) (hs0 : s ≠ 0) {ι : Type} [Finite ι] (f : ι → R)
    (hf : ∀ j, f j ∈ 𝒜 (N * a)) {Pt : Type} (ev : Pt → (R →ₐ[K] K))
    (hcov : ∀ p, ∃ i, ev p (x i) ≠ 0)
    (hpt : ∀ (v : Fin m → K) (i : Fin m), v i = 1 →
      (∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → aeval x G = 0 → aeval v G = 0) →
      ∃ p, ev p (x i) ≠ 0 ∧ ∀ j, ev p (x j) = v j * ev p (x i))
    (hsep : ∀ p q (c : K), (∀ j, ev p (x j) = c * ev q (x j)) → p = q)
    (Z : Set Pt) (hZ : Z.Finite) (hZf : ∀ p, p ∈ Z ↔ ∀ j, ev p (f j) = 0) :
    Nat.card {p : Pt // p ∈ Z ∧ ev p s = 0} ≤ N ^ g * g.factorial * d * a ^ (g - 1) := by
  classical
  let S : Set R := Set.range x ∪ ({s} ∪ Set.range f)
  have hS : ∀ y ∈ S, ∃ e, y ∈ 𝒜 (N * e) := by
    rintro y (⟨j, rfl⟩ | rfl | ⟨j, rfl⟩)
    · exact ⟨1, by simpa using hx j⟩
    · exact ⟨d, hs⟩
    · exact ⟨a, hf j⟩
  have hSfin : S.Finite := (Set.finite_range x).union ((Set.finite_singleton s).union (Set.finite_range f))
  obtain ⟨inst⟩ := nonempty_gradedAlgebra_subGrading 𝒜 hN S hS
  set T := Algebra.adjoin K S with hT
  set ℬ := subGrading 𝒜 N T with hℬ
  let x' : Fin m → T := fun j => ⟨x j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
  let s' : T := ⟨s, Algebra.subset_adjoin (Or.inr (Or.inl rfl))⟩
  let f' : ι → T := fun j => ⟨f j, Algebra.subset_adjoin (Or.inr (Or.inr ⟨j, rfl⟩))⟩
  have hx' : ∀ j, x' j ∈ ℬ 1 := fun j => by
    rw [hℬ, mem_subGrading]
    simpa using hx j
  have hval : ∀ G : MvPolynomial (Fin m) K, ((aeval x' G : T) : R) = aeval x G := fun G =>
    comp_aeval_apply x' T.val G
  have hform' : ∀ e, ∀ y ∈ ℬ e, ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K),
      G.IsHomogeneous (n + e) ∧ y * x' i ^ n = aeval x' G := fun e y hy i => by
    obtain ⟨n, G, hG, h⟩ := hform e y hy i
    exact ⟨n, G, hG, Subtype.ext (by rw [hval, ← h]; rfl)⟩
  haveI : Algebra.FiniteType K T := Algebra.FiniteType.adjoin_of_finite hSfin
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range x')) T := ⟨fun y => by
    induction y using DirectSum.Decomposition.inductionOn ℬ with
    | zero => exact isIntegral_zero
    | @homogeneous e y =>
      refine hInt T ℬ m x' hx' ⟨i₀, fun h => hx₀ (congrArg Subtype.val h)⟩ e y y.2 fun i => ?_
      obtain ⟨n, G, -, h⟩ := hform' e y y.2 i
      refine ⟨n, ?_⟩
      rw [h, Algebra.adjoin_range_eq_range_aeval]
      exact ⟨G, rfl⟩
    | add a b ha hb => exact ha.add hb⟩
  haveI : Algebra.FiniteType (Algebra.adjoin K (Set.range x')) T :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  have hdim : ringKrullDim T = (g + 1 : ℕ) :=
    ringKrullDim_cone ℬ hx' r i₀ hi₀ hr (fun n G hG => by
      rw [← hrel n G hG, ← hval]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩) g hC
  haveI : Finite {p : Pt // p ∈ Z ∧ ev p s = 0} :=
    (hZ.subset (fun p hp => hp.1 : {p | p ∈ Z ∧ ev p s = 0} ⊆ Z)).to_subtype
  let E := (Finite.equivFin {p : Pt // p ∈ Z ∧ ev p s = 0}).symm
  refine hBez T ℬ m g N d a x' s' (Set.range f') hg hx' Algebra.IsIntegral.finite hdim
    (fun e he => ?_) hs (fun h => hs0 (congrArg Subtype.val h)) ?_
    ⟨(fun p => (ev p).comp T.val) '' Z, hZ.image _, fun φ hφ hφf => ?_⟩ _
    (fun j => (ev (E j).1).comp T.val) (fun j => hcov _) (fun j => ⟨(E j).2.2, ?_⟩) ?_
  · obtain ⟨h1, h2⟩ := hfin e he
    refine le_trans ?_ h2
    refine LinearMap.finrank_le_finrank_of_injective
      (f := T.val.toLinearMap.restrict (p := ℬ e) (q := 𝒜 (N * e)) fun y hy => hy) fun y z h => ?_
    have h3 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h3)
  · rintro _ ⟨j, rfl⟩
    exact hf j
  · obtain ⟨i, hi⟩ := hφ
    obtain ⟨p, hp, hp'⟩ := hpt (fun j => φ (x' j) * (φ (x' i))⁻¹) i (mul_inv_cancel₀ hi)
      fun n G hG h => by
        have h0 : aeval x' G = 0 := Subtype.ext (by rw [hval, h]; rfl)
        rw [aeval_mul_of_isHomogeneous _ _ hG, ← comp_aeval_apply, h0, map_zero, zero_mul]
    have hc : ∀ e, ∀ y ∈ ℬ e, φ y = (φ (x' i) * (ev p (x i))⁻¹) ^ e * (ev p).comp T.val y :=
      fun e y hy => by
        obtain ⟨n, G, hG, h⟩ := hform' e y hy i
        refine map_eq_pow_mul (fun j => ?_) hi hG h
        change _ = ev p (x j) * _
        rw [hp' j]
        field_simp
    refine ⟨_, ⟨p, (hZf p).2 fun j => ?_, rfl⟩, _, hc⟩
    have h1 := hc a (f' j) (hf j)
    rw [hφf _ ⟨j, rfl⟩] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (mul_ne_zero hi (inv_ne_zero hp)))
  · rintro _ ⟨l, rfl⟩
    exact (hZf _).1 (E j).2.1 l
  · rintro j j' ⟨c, hc⟩
    refine E.injective (Subtype.ext (hsep _ _ c fun l => ?_).symm)
    simpa using hc 1 _ (hx' l)
end GlobalTheory.TorsionZero
