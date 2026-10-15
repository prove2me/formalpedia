-- Prove2me | solution 1 for OAI.BogomolovPop.perfect_scalar_iterates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:41:59.552001+00:00
-- url     : https://prove2.me/submissions/312367e0-b6c6-43a4-b81b-b8044952ab73

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/Injectivity.lean:L143-L207
-- (upload_full_project.md Phase 4): solution for node OAI.BogomolovPop.perfect_scalar_iterates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
import Definitions.Def_OAI_Algebra_BogomolovPop_Kummer
import Definitions.Def_OAI_Algebra_BogomolovPop_Injectivity
import Theorems.Thm_OAI_BogomolovPop_conjugation_kummer_scalar
import Theorems.Thm_OAI_BogomolovPop_kummer_endomorphism_frobenius

-- ---- from OAI.Algebra.BogomolovPop.Injectivity ----
namespace OAI

/-! Perfect-closure descent and injectivity of the canonical orbit map. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

lemma purely_inseparable_pow_mem_mono
    (F E : Type*) [Field F] [Field E] [Algebra F E] (q : ℕ)
    {x : E} {n m : ℕ} (h : x ^ q ^ n ∈ (algebraMap F E).range) (hnm : n ≤ m) :
    x ^ q ^ m ∈ (algebraMap F E).range := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y ^ (q ^ (m - n)), ?_⟩
  rw [map_pow, hy, ← pow_mul, ← pow_add, Nat.add_sub_of_le hnm]

theorem uniform_frobenius_clearing
    (k F E : Type*) [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
    [Algebra.EssFiniteType k F] [IsPurelyInseparable F E]
    (q : ℕ) [ExpChar F q] (σ : F →+* E)
    (hc : ∀ c : k, ∃ d : k, σ (algebraMap k F c) = algebraMap k E d) :
    ∃ n : ℕ, ∃ φ : F →+* F, ∀ x : F,
      algebraMap F E (φ x) = (σ x) ^ (q ^ n) := by
  classical
  let : ExpChar E q := expChar_of_injective_algebraMap (algebraMap F E).injective q
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k F
  choose e he using fun x : F => IsPurelyInseparable.pow_mem F q (σ x)
  let n := s.sup e
  let ψ : F →+* E := (iterateFrobenius E q n).comp σ
  let S : IntermediateField k F := ((algebraMap F E).fieldRange.comap ψ).toIntermediateField
    (by
      intro c
      obtain ⟨d, hd⟩ := hc c
      change ψ (algebraMap k F c) ∈ (algebraMap F E).fieldRange
      refine ⟨(algebraMap k F d) ^ (q ^ n), ?_⟩
      simp only [ψ, RingHom.comp_apply, iterateFrobenius_def, hd, map_pow,
        ← IsScalarTower.algebraMap_apply k F E])
  have hS : S = ⊤ := by
    apply top_le_iff.mp
    rw [← hs, IntermediateField.adjoin_le_iff]
    intro x hx
    change σ x ^ (q ^ n) ∈ (algebraMap F E).fieldRange
    exact purely_inseparable_pow_mem_mono F E q (he x) (Finset.le_sup hx)
  have hψ : ∀ x : F, ψ x ∈ (algebraMap F E).fieldRange := by
    intro x
    change x ∈ S
    simp [hS]
  let φ : F →+* F := ((algebraMap F E).rangeRestrictFieldEquiv.symm.toRingHom).comp
    (ψ.codRestrict _ hψ)
  refine ⟨n, φ, ?_⟩
  intro x
  exact congrArg (fun z : (algebraMap F E).fieldRange => (z : E))
    ((algebraMap F E).rangeRestrictFieldEquiv.apply_symm_apply ⟨ψ x, hψ x⟩)

end BogomolovPop

namespace BogomolovPop
lemma purely_inseparable_ringHom_ext
    {F E T : Type*} [Field F] [Field E] [Field T]
    [Algebra F E] [IsPurelyInseparable F E]
    (q : ℕ) [ExpChar F q] [ExpChar T q]
    (f g : E →+* T) (h : ∀ x : F, f (algebraMap F E x) = g (algebraMap F E x)) : f = g := by
  ext x
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem F q x
  apply (iterateFrobenius T q n).injective
  simp only [iterateFrobenius_def, ← map_pow, ← hy, h]

end BogomolovPop
namespace BogomolovPop
open scoped Topology
theorem perfect_scalar_iterates (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    [Algebra.EssFiniteType k F] (hchar : (ell : F) ≠ 0)
    (q : ℕ) [ExpChar F q] (δ : PerfectIsom k F k F)
    (β : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (hβ : ∀ x : PerfectFieldClosure F, β x = (δ.1 x : AlgebraicClosure F))
    (u : (PadicInt ell)ˣ)
    (hg : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∃ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (∀ x, β (τ x) = σ (β x)) ∧
        Filter.Tendsto (fun n : ℕ => absoluteToPiA ell F σ ^ (u : PadicInt ell).appr n)
          Filter.atTop (nhds (absoluteToPiA ell F τ)))
    (hx : ∃ x : F, Transcendental k x) :
    ∃ n m : ℕ, ∀ x : PerfectFieldClosure F, (δ.1 x) ^ (q ^ n) = x ^ (q ^ m) := by
  let P : Type _ := PerfectFieldClosure F
  let A := AlgebraicClosure F
  let : ExpChar P q := expChar_of_injective_algebraMap (algebraMap F P).injective q
  let : ExpChar A q := expChar_of_injective_algebraMap (algebraMap F A).injective q
  let σ : F →+* P := δ.1.toRingHom.comp (algebraMap F P)
  have hc : ∀ c : k, ∃ d : k, σ (algebraMap k F c) = algebraMap k P d := by
    intro c
    have hm : δ.1 (algebraMap k P c) ∈ Set.range (algebraMap k P) := by
      have hs : δ.1 '' Set.range (algebraMap k P) ⊆ Set.range (algebraMap k P) := le_of_eq δ.2
      exact hs ⟨algebraMap k P c, ⟨c, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := hm
    refine ⟨d, ?_⟩
    change δ.1 (algebraMap F P (algebraMap k F c)) = _
    rw [← IsScalarTower.algebraMap_apply k F P]
    exact hd.symm
  obtain ⟨n, φ, hφ⟩ := uniform_frobenius_clearing k F P q σ hc
  let γ : A ≃+* A := β.trans (iterateFrobeniusEquiv A q n)
  have hγ : ∀ x : F, γ (algebraMap F A x) = algebraMap F A (φ x) := by
    intro x
    change (β (algebraMap F A x)) ^ (q ^ n) = _
    change (β ((algebraMap F P x : P) : A)) ^ (q ^ n) = _
    rw [hβ]
    have hh := congrArg (algebraMap P A) (hφ x)
    rw [map_pow] at hh
    exact hh.symm
  have hγg : ∀ ρ : A ≃ₐ[F] A, ∃ τ : A ≃ₐ[F] A,
      (∀ x, γ (τ x) = ρ (γ x)) ∧
      Filter.Tendsto (fun n : ℕ => absoluteToPiA ell F ρ ^ (u : PadicInt ell).appr n)
        Filter.atTop (nhds (absoluteToPiA ell F τ)) := by
    intro ρ
    obtain ⟨τ, hτ, hlim⟩ := hg ρ
    refine ⟨τ, ?_, hlim⟩
    intro x
    change (β (τ x)) ^ (q ^ n) = ρ ((β x) ^ (q ^ n))
    rw [hτ, map_pow]
  obtain ⟨a, ha⟩ := conjugation_kummer_scalar ell k F hchar φ γ hγ u hγg
  have he : ∃ m : ℕ, ∀ x : F, φ x = x ^ (q ^ m) := by
    rcases kummer_endomorphism_frobenius ell k F φ a hx ha with hid | ⟨p, r, hp, hpF, hr⟩
    · exact ⟨0, fun x => by simp [hid]⟩
    · have : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hpF
      have hpq : p = q := ExpChar.eq (R := F) (ExpChar.prime hp) inferInstance
      exact ⟨r, hpq ▸ hr⟩
  obtain ⟨m, hm⟩ := he
  refine ⟨n, m, ?_⟩
  have heq : (iterateFrobenius P q n).comp δ.1.toRingHom = iterateFrobenius P q m := by
    apply purely_inseparable_ringHom_ext (F := F) q
    intro x
    change (σ x) ^ (q ^ n) = (algebraMap F P x) ^ (q ^ m)
    rw [← hφ x, hm, map_pow]
  intro x
  exact DFunLike.congr_fun heq x
end BogomolovPop

namespace BogomolovPop
open scoped Topology

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
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    [Algebra.EssFiniteType k F] (hchar : (ell : F) ≠ 0)
    (q : ℕ) [ExpChar F q] (δ : PerfectIsom k F k F)
    (β : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (hβ : ∀ x : PerfectFieldClosure F, β x = (δ.1 x : AlgebraicClosure F))
    (u : (PadicInt ell)ˣ)
    (hg : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∃ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (∀ x, β (τ x) = σ (β x)) ∧
        Filter.Tendsto (fun n : ℕ => absoluteToPiA ell F σ ^ (u : PadicInt ell).appr n)
          Filter.atTop (nhds (absoluteToPiA ell F τ)))
    (hx : ∃ x : F, Transcendental k x) :
    ∃ n m : ℕ, ∀ x : PerfectFieldClosure F, (δ.1 x) ^ (q ^ n) = x ^ (q ^ m) := by
  first
    | exact OAI.BogomolovPop.perfect_scalar_iterates ell k F hchar q δ β hβ u hg hx
    | exact OAI.BogomolovPop.perfect_scalar_iterates
    | (apply OAI.BogomolovPop.perfect_scalar_iterates <;> assumption)
    | (intros; apply OAI.BogomolovPop.perfect_scalar_iterates <;> assumption)
