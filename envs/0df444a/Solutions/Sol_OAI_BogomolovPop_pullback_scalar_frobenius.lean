-- Prove2me | solution 1 for OAI.BogomolovPop.pullback_scalar_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:43:36.399275+00:00
-- url     : https://prove2.me/submissions/3204b483-c143-4a51-b611-53b380db0efa

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/Injectivity.lean:L213-L274
-- (upload_full_project.md Phase 4): solution for node OAI.BogomolovPop.pullback_scalar_frobenius. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
import Definitions.Def_OAI_Algebra_BogomolovPop_Kummer
import Definitions.Def_OAI_Algebra_BogomolovPop_Injectivity
import Theorems.Thm_OAI_BogomolovPop_perfect_scalar_iterates

-- ---- from OAI.Algebra.BogomolovPop.Injectivity ----
namespace OAI

/-! Perfect-closure descent and injectivity of the canonical orbit map. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

end BogomolovPop

namespace BogomolovPop
lemma frobeniusPerfectIsom_eqvGen
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed l]
    (q : ℕ) [ExpChar L q] (n : ℕ) (α : PerfectIsom k K l L) :
    Relation.EqvGen FrobeniusStep α (frobeniusPerfectIsom q n α) := by
  induction n with
  | zero =>
    have he : frobeniusPerfectIsom q 0 α = α := by
      apply Subtype.ext; apply RingEquiv.ext; intro x
      simp
    rw [he]
    exact Relation.EqvGen.refl _
  | succ n ih =>
    apply Relation.EqvGen.trans _ _ _ ih
    rcases expChar_is_prime_or_one L q with hp | rfl
    · apply Relation.EqvGen.rel
      refine ⟨q, hp, ?_, ?_⟩
      · have : CharP L q := by
          cases (inferInstance : ExpChar L q) with
          | zero => exact False.elim (hp.ne_one rfl)
          | prime hp => infer_instance
        exact CharP.cast_eq_zero L q
      · intro x
        simp only [frobeniusPerfectIsom_apply, pow_succ, pow_mul]
    · have he : frobeniusPerfectIsom 1 (n + 1) α = frobeniusPerfectIsom 1 n α := by
        apply Subtype.ext; apply RingEquiv.ext; intro x
        simp
      rw [he]
      exact Relation.EqvGen.refl _

theorem frobenius_orbit_of_iterates
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed l]
    (q : ℕ) [ExpChar L q] (α β : PerfectIsom k K l L)
    (n m : ℕ) (h : ∀ x, (α.1 x) ^ (q ^ n) = (β.1 x) ^ (q ^ m)) :
    Relation.EqvGen FrobeniusStep α β := by
  have he : frobeniusPerfectIsom q n α = frobeniusPerfectIsom q m β := by
    apply Subtype.ext; apply RingEquiv.ext; intro x
    exact h x
  exact Relation.EqvGen.trans _ _ _ (frobeniusPerfectIsom_eqvGen q n α)
    (he ▸ Relation.EqvGen.symm _ _ (frobeniusPerfectIsom_eqvGen q m β))
end BogomolovPop
namespace BogomolovPop
open scoped Topology
end BogomolovPop

namespace BogomolovPop
open scoped Topology

theorem pullback_scalar_frobenius (ell : ℕ) [Fact ell.Prime]
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed k] [IsAlgClosed l]
    [Algebra.EssFiniteType k K]
    (hchar : (ell : K) ≠ 0) (hx : ∃ x : K, Transcendental k x)
    (α β : PerfectIsom k K l L) (φ χ : IsomC ell K L)
    (hφ : PullbackGraph α φ) (hχ : PullbackGraph β χ)
    (hu : ScalarStep φ χ) : Relation.EqvGen FrobeniusStep α β := by
  obtain ⟨a, ha, hfa⟩ := hφ
  obtain ⟨b, hb, hfb⟩ := hχ
  obtain ⟨u, hu⟩ := hu
  let δ : PerfectIsom k K k K := ⟨β.1.trans α.1.symm, by
    calc (α.1.symm ∘ β.1) '' Set.range (algebraMap k (PerfectFieldClosure K)) =
        α.1.symm '' (β.1 '' Set.range (algebraMap k (PerfectFieldClosure K))) := Set.image_comp _ _ _
      _ = α.1.symm '' Set.range (algebraMap l (PerfectFieldClosure L)) := congrArg _ β.2
      _ = α.1.symm '' (α.1 '' Set.range (algebraMap k (PerfectFieldClosure K))) := congrArg _ α.2.symm
      _ = Set.range (algebraMap k (PerfectFieldClosure K)) := by
        simp only [Set.image_image, RingEquiv.symm_apply_apply]
        exact Set.image_id _⟩
  let γ : AlgebraicClosure K ≃+* AlgebraicClosure K := b.trans a.symm
  have hγ : ∀ x : PerfectFieldClosure K, γ x = (δ.1 x : AlgebraicClosure K) := by
    intro x
    change a.symm (b x) = _
    rw [hb, perfectExtension_symm α.1 a ha]
    rfl
  have hγg : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∃ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        (∀ x, γ (τ x) = σ (γ x)) ∧
        Filter.Tendsto (fun n : ℕ => absoluteToPiA ell K σ ^ (u : PadicInt ell).appr n)
          Filter.atTop (nhds (absoluteToPiA ell K τ)) := by
    intro σ
    obtain ⟨ρ, hρ⟩ := (absoluteConjugateEquiv α.1 a ha).surjective σ
    change absoluteConjugate α.1 a ha ρ = σ at hρ
    obtain ⟨τ, hτ, hχτ⟩ := hfb ρ
    change AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K at τ
    change (∀ x, b (τ x) = ρ (b x)) at hτ
    obtain ⟨ν, hν, hφν⟩ := hfa ρ
    have hνσ : ν = σ := by
      rw [← hρ]
      apply AlgEquiv.ext
      intro x
      apply a.injective
      exact (hν x).trans (a.apply_symm_apply _).symm
    refine ⟨τ, ?_, ?_⟩
    · intro x
      change a.symm (b (τ x)) = σ (a.symm (b x))
      rw [hτ, ← hρ, absoluteConjugate_apply, a.apply_symm_apply]
    · have ht := hu (absoluteToPiA ell L ρ)
      rw [hφν, hνσ, hχτ] at ht
      exact ht
  obtain ⟨q, hq⟩ := ExpChar.exists K
  let := hq
  let : ExpChar (AlgebraicClosure K) q :=
    expChar_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q
  let : ExpChar (AlgebraicClosure L) q := expChar_of_injective_ringHom (f := a.toRingHom) a.injective q
  let : ExpChar L q := (algebraMap L (AlgebraicClosure L)).expChar
    (algebraMap L (AlgebraicClosure L)).injective q
  obtain ⟨n, m, hm⟩ := perfect_scalar_iterates ell k K hchar q δ γ hγ u hγg hx
  apply frobenius_orbit_of_iterates q α β m n
  intro x
  have he := congrArg α.1 (hm x)
  simpa only [map_pow, δ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply] using he.symm

end BogomolovPop

namespace BogomolovPop

end BogomolovPop

end
end

end OAI

-- ---- platform node ----
open OAI OAI.BogomolovPop
open scoped Topology
open scoped Topology

theorem solution (ell : ℕ) [Fact ell.Prime]
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed k] [IsAlgClosed l]
    [Algebra.EssFiniteType k K]
    (hchar : (ell : K) ≠ 0) (hx : ∃ x : K, Transcendental k x)
    (α β : PerfectIsom k K l L) (φ χ : IsomC ell K L)
    (hφ : PullbackGraph α φ) (hχ : PullbackGraph β χ)
    (hu : ScalarStep φ χ) : Relation.EqvGen FrobeniusStep α β := by
  first
    | exact OAI.BogomolovPop.pullback_scalar_frobenius ell hchar hx α β φ χ hφ hχ hu
    | exact OAI.BogomolovPop.pullback_scalar_frobenius
    | (apply OAI.BogomolovPop.pullback_scalar_frobenius <;> assumption)
    | (intros; apply OAI.BogomolovPop.pullback_scalar_frobenius <;> assumption)
