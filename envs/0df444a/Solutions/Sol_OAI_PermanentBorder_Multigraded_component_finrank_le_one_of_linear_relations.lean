-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.component_finrank_le_one_of_linear_relations
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:25:36.312702+00:00
-- url     : https://prove2.me/submissions/de639344-16c4-442e-a643-d4e5a82b60b0

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Multigraded.lean:L301-L354
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.component_finrank_le_one_of_linear_relations. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded

-- ---- from OAI.Algebra.Determinantal.Multigraded ----
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma weight_blockExponent (group : σ → ι) (m : σ →₀ ℕ) (j : ι) :
    Finsupp.weight (blockWeight group) m j = (blockExponent group m j : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, blockWeight, nsmul_eq_mul]
  simp [blockExponent, Pi.single_apply, Finset.sum_filter, eq_comm]

lemma prod_blockExponent {S : Type*} [CommMonoid S] (group : σ → ι)
    (m : σ →₀ ℕ) (z : ι → S) :
    ∏ v, z (group v) ^ m v = ∏ j, z j ^ blockExponent group m j := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ group]
  apply Finset.prod_congr rfl
  intro j _
  rw [blockExponent, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

omit [Fintype σ] [Fintype ι] in
lemma componentEmbed_injective (group : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) : Function.Injective (componentEmbed group I d) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
    ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
  change Submodule.Quotient.mk p = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

theorem component_finrank_le_one_of_linear_relations (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (z : ι → MvPolynomial σ K) (c : σ → K)
    (hrel : ∀ v, X v - C (c v) * z (group v) ∈ I) (d : ι → ℤ) :
    Module.finrank K (componentQuotient (blockWeight group) I d) ≤ 1 := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let Z := ∏ j, q (z j) ^ (d j).toNat
  have hX (v : σ) : q (X v) = algebraMap K _ (c v) * q (z (group v)) := by
    have h := Ideal.Quotient.eq.mpr (hrel v)
    change q (X v) = q (C (c v) * z (group v)) at h
    rw [map_mul] at h
    exact h.trans (congrArg (· * q (z (group v))) (q.commutes (c v)))
  have hmon (m : σ →₀ ℕ) (r : K) (hm : Finsupp.weight (blockWeight group) m = d) :
      q (monomial m r) ∈ Submodule.span K {Z} := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r * ∏ v, c v ^ m v, ?_⟩
    have hexp : ∀ j, blockExponent group m j = (d j).toNat := by
      intro j
      have h := congrFun hm j
      rw [weight_blockExponent] at h
      rw [← h, Int.toNat_natCast]
    rw [monomial_eq, Finsupp.prod_pow, map_mul, map_prod]
    simp only [map_pow, hX, mul_pow, Finset.prod_mul_distrib]
    rw [prod_blockExponent group m (fun j => q (z j))]
    simp only [hexp]
    change (r * ∏ v, c v ^ m v) • Z =
      algebraMap K _ r * ((∏ v, (algebraMap K _ (c v)) ^ m v) * Z)
    have he : (r * ∏ v, c v ^ m v) • Z =
        algebraMap K (MvPolynomial σ K ⧸ I) (r * ∏ v, c v ^ m v) * Z :=
      Algebra.smul_def (R := K) (A := MvPolynomial σ K ⧸ I) (r * ∏ v, c v ^ m v) Z
    rw [he, map_mul, map_prod]
    simp only [map_pow]
    ring
  have hpiece (p : Piece (K := K) (blockWeight group) d) :
      q p.val ∈ Submodule.span K {Z} := by
    rcases p with ⟨p,hp⟩
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p₁ p₂ _ _ h₁ h₂ => simpa only [map_add] using Submodule.add_mem _ h₁ h₂
    | monomial m r hm => exact hmon m r hm
  let f := (componentEmbed group I d).codRestrict (Submodule.span K {Z}) (by
    intro x
    obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
      ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
    exact hpiece p)
  have hf : Function.Injective f := fun a b h =>
    componentEmbed_injective group I d (congrArg Subtype.val h)
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans
    (by
      apply finrank_le_one_iff.mpr
      refine ⟨⟨Z, Submodule.subset_span (Set.mem_singleton Z)⟩, ?_⟩
      intro x
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp x.property
      exact ⟨c, Subtype.ext hc⟩)

end LinearLeaves
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.component_finrank_le_one_of_linear_relations := @_root_.OAI.PermanentBorder.Multigraded.component_finrank_le_one_of_linear_relations
