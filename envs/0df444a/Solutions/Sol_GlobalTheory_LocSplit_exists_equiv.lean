-- Prove2me | solution 1 for GlobalTheory.LocSplit.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:04.255327+00:00
-- url     : https://prove2.me/submissions/62a32775-9bea-4e91-ac24-daebd4887bb5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
namespace GlobalTheory.LocSplit
theorem _root_.solution {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    (hr : Module.finrank K A = 2) (cj : A ≃ₐ[K] A) (t : A) (β : K) (hβ : β ≠ 0)
    (ht : t ^ 2 = algebraMap K A (β ^ 2)) (hc : cj t = -t)
    (hsp : ∀ y : A, ∃ u v : K, y = algebraMap K A u + algebraMap K A v * t) :
    ∃ e : A ≃ₐ[K] K × K, ∀ x, e (cj x) = (e x).swap := by
  haveI : FiniteDimensional K A := Module.finite_of_finrank_pos (by omega)
  let gl : K × K →ₗ[K] A :=
    { toFun := fun z => algebraMap K A ((z.1 + z.2) / 2) +
        algebraMap K A ((z.1 - z.2) / (2 * β)) * t
      map_add' := fun x y => by
        have h1 : ((x + y).1 + (x + y).2) / 2 = (x.1 + x.2) / 2 + (y.1 + y.2) / 2 := by
          simp; ring
        have h2 : ((x + y).1 - (x + y).2) / (2 * β) =
            (x.1 - x.2) / (2 * β) + (y.1 - y.2) / (2 * β) := by simp; ring
        rw [h1, h2, map_add, map_add]; ring
      map_smul' := fun c x => by
        have h1 : ((c • x).1 + (c • x).2) / 2 = c * ((x.1 + x.2) / 2) := by simp; ring
        have h2 : ((c • x).1 - (c • x).2) / (2 * β) = c * ((x.1 - x.2) / (2 * β)) := by simp; ring
        rw [h1, h2, map_mul, map_mul, RingHom.id_apply, Algebra.smul_def]; ring }
  have hgl : ∀ z : K × K, gl z = algebraMap K A ((z.1 + z.2) / 2) +
        algebraMap K A ((z.1 - z.2) / (2 * β)) * t := fun _ => rfl
  let g : K × K →ₐ[K] A := AlgHom.ofLinearMap gl (by rw [hgl]; simp) (fun x y => by
    have h1 : ((x * y).1 + (x * y).2) / 2 = ((x.1 + x.2) / 2) * ((y.1 + y.2) / 2) +
      ((x.1 - x.2) / (2 * β)) * ((y.1 - y.2) / (2 * β)) * β ^ 2 := by
      simp only [Prod.fst_mul, Prod.snd_mul]; field_simp; ring
    have h2 : ((x * y).1 - (x * y).2) / (2 * β) = ((x.1 + x.2) / 2) * ((y.1 - y.2) / (2 * β)) +
      ((x.1 - x.2) / (2 * β)) * ((y.1 + y.2) / 2) := by
      simp only [Prod.fst_mul, Prod.snd_mul]; field_simp; ring
    rw [hgl, hgl, hgl, h1, h2]
    simp only [map_add, map_mul, ← ht]
    ring)
  have hsurj : Function.Surjective gl := by
    intro y
    obtain ⟨u, v, rfl⟩ := hsp y
    refine ⟨(u + v * β, u - v * β), ?_⟩
    rw [hgl]
    congr 2
    · ring
    · congr 1; field_simp; ring
  have hinj : Function.Injective gl :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).2 hsurj
  let e := AlgEquiv.ofBijective g ⟨hinj, hsurj⟩
  refine ⟨e.symm, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := e.surjective x
  rw [e.symm_apply_apply, AlgEquiv.symm_apply_eq]
  change cj (gl z) = gl z.swap
  rw [hgl, hgl, map_add, map_mul, cj.commutes, cj.commutes, hc]
  have h2 : (z.swap.1 - z.swap.2) / (2 * β) = -((z.1 - z.2) / (2 * β)) := by simp; ring
  rw [h2, map_neg, Prod.fst_swap, Prod.snd_swap, add_comm z.2]
  ring
end GlobalTheory.LocSplit
