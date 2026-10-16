-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.component_finrank_zero_of_block_killed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:27:20.429644+00:00
-- url     : https://prove2.me/submissions/06bc01b8-54ee-4e72-b40b-aabb7de97217

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Multigraded.lean:L356-L389
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.component_finrank_zero_of_block_killed. The node keeps its source
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

theorem component_finrank_zero_of_block_killed (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (j : ι)
    (hkill : ∀ v, group v = j → X v ∈ I) (d : ι → ℤ) (hd : 0 < d j) :
    Module.finrank K (componentQuotient (blockWeight group) I d) = 0 := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  have hmon (m : σ →₀ ℕ) (r : K) (hm : Finsupp.weight (blockWeight group) m = d) :
      q (monomial m r) = 0 := by
    have hexp : 0 < blockExponent group m j := by
      have h := congrFun hm j
      rw [weight_blockExponent] at h
      omega
    obtain ⟨v,hv,hmv⟩ := Finset.sum_pos_iff.mp hexp
    have hqv : q (X v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (hkill v (Finset.mem_filter.mp hv).2)
    rw [monomial_eq, Finsupp.prod_pow, map_mul, map_prod]
    have hz : ∏ v, q (X v ^ m v) = 0 := Finset.prod_eq_zero (Finset.mem_univ v) (by
      rw [map_pow, hqv, zero_pow (Nat.ne_of_gt hmv)])
    rw [hz, mul_zero]
  have hpiece (p : Piece (K := K) (blockWeight group) d) : q p.val = 0 := by
    rcases p with ⟨p,hp⟩
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => exact map_zero q
    | add p₁ p₂ _ _ h₁ h₂ => rw [map_add, h₁,h₂,add_zero]
    | monomial m r hm => exact hmon m r hm
  apply Module.finrank_eq_zero_iff.mpr
  intro x
  refine ⟨1,one_ne_zero,?_⟩
  rw [one_smul]
  apply componentEmbed_injective group I d
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
    ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
  rw [map_zero]
  exact hpiece p

end LinearLeaves
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.component_finrank_zero_of_block_killed := @_root_.OAI.PermanentBorder.Multigraded.component_finrank_zero_of_block_killed
