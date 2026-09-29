-- Prove2me | solution 1 for Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/682031cd-0595-5193-b8ec-16f0d0aa4522

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct
open TensorProduct

namespace GrassCoverS1b

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ}
variable {ι : Type} (g : ι → M)
variable {K : Type} [Field K] [Algebra R K]

lemma span_mkQ_tmul_eq_top (hg : Submodule.span R (Set.range g) = ⊤) (N : Submodule K (K ⊗[R] M)) :
    Submodule.span K (Set.range fun t => N.mkQ ((1 : K) ⊗ₜ[R] g t)) = ⊤ := by
  have h1 : Submodule.span K (Set.range fun t => (1 : K) ⊗ₜ[R] g t) = ⊤ := by
    have := Submodule.baseChange_span (R := R) (A := K) (M := M) (Set.range g)
    rw [hg, Submodule.baseChange_top] at this
    rw [this, ← Set.range_comp]
    rfl
  have h2 : Set.range (fun t => N.mkQ ((1 : K) ⊗ₜ[R] g t)) = N.mkQ '' Set.range fun t => (1 : K) ⊗ₜ[R] g t := by
    rw [← Set.range_comp]; rfl
  rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]

lemma finrank_quotient_eq (N : Module.Grassmannian K (K ⊗[R] M) k) :
    Module.finrank K ((K ⊗[R] M) ⧸ N.toSubmodule) = k := by
  have h := N.rankAtStalk_eq ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact_mod_cast h

theorem cover (hg : Submodule.span R (Set.range g) = ⊤) (N : Module.Grassmannian K (K ⊗[R] M) k) :
    ∃ I : Fin k → ι, Function.Injective I ∧
      Function.Bijective fun v : Fin k → K =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i)) := by
  classical
  set w : ι → (K ⊗[R] M) ⧸ N.toSubmodule := fun t => N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g t) with hw
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K w
  rw [span_mkQ_tmul_eq_top g hg] at hsp

  let b : Module.Basis κ K ((K ⊗[R] M) ⧸ N.toSubmodule) := Module.Basis.mk hli (by rw [hsp])
  haveI : Finite κ := Module.Finite.finite_basis b
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← finrank_quotient_eq N, Module.finrank_eq_card_basis b]
  let e : κ ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin k) K ((K ⊗[R] M) ⧸ N.toSubmodule) := b.reindex e
  have hb' : ∀ i, b' i = w (a (e.symm i)) := fun i => by
    simp [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]
  refine ⟨fun i => a (e.symm i), ha.comp e.symm.injective, ?_⟩
  have hfun : (fun v : Fin k → K => ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (a (e.symm i)))) =
      b'.equivFun.symm := by
    funext v
    rw [Module.Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [hb']
  rw [hfun]
  exact b'.equivFun.symm.bijective

end GrassCoverS1b

theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (K : Type) [Field K] [Algebra R K] (N : Module.Grassmannian K (K ⊗[R] M) k) :
    ∃ I : Fin k → ι, Function.Injective I ∧
      Function.Bijective fun v : Fin k → K =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i)) :=
  GrassCoverS1b.cover g hg N

end S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top
end P2MW
export P2MW.S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top (solution)
