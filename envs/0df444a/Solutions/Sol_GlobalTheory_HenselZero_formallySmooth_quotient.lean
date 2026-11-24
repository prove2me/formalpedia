-- Prove2me | solution 1 for GlobalTheory.HenselZero.formallySmooth_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:19.91817+00:00
-- url     : https://prove2.me/submissions/da602686-1dbe-4bb6-ba97-516a92dc1a79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_addDers_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
open IsLocalRing GlobalTheory.SqZero
namespace GlobalTheory.HenselZero
theorem _root_.solution {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) (τ : ι → Derivation R S S)
    (h : IsUnit (Matrix.of fun i k => τ k (f i)).det) :
    Algebra.FormallySmooth R (S ⧸ Ideal.span (Set.range f)) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_
  obtain ⟨g', hg'⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (g.comp (Ideal.Quotient.mkₐ R _))
  have hg : ∀ a, Ideal.Quotient.mk I (g' a) = g (Ideal.Quotient.mk _ a) := fun a => congr($hg' a)
  have hf : ∀ i, g' (f i) ∈ I := fun i => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  let M : Matrix ι ι B := Matrix.of fun i k => g' (τ k (f i))
  have hM : IsUnit M.det := by
    have := h.map g'
    rw [AlgHom.map_det] at this
    exact this
  let t : ι → B := M⁻¹.mulVec fun i => - g' (f i)
  have ht : ∀ k, t k ∈ I := fun k => Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (neg_mem (hf i))
  have hMt : M.mulVec t = fun i => - g' (f i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  have h0 : ∀ i j, t i * t j = 0 := fun i j => by
    have := Ideal.mul_mem_mul (ht i) (ht j)
    rwa [← sq, hI] at this
  refine ⟨Ideal.Quotient.liftₐ _ (addDers τ g' t h0) fun a ha => ?_, ?_⟩
  · refine (Ideal.span_le (I := RingHom.ker (addDers τ g' t h0))).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    have : ∑ k, g' (τ k (f i)) * t k = - g' (f i) := congrFun hMt i
    show addDers τ g' t h0 (f i) = 0
    rw [addDers_apply, this, add_neg_cancel]
  · refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => ?_)
    show Ideal.Quotient.mk I (addDers τ g' t h0 a) = g (Ideal.Quotient.mk _ a)
    rw [addDers_apply, map_add, hg, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (ht k)), add_zero]
end GlobalTheory.HenselZero
