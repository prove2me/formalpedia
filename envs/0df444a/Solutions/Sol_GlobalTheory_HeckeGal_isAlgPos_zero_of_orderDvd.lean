-- Prove2me | solution 1 for GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:10.441505+00:00
-- url     : https://prove2.me/submissions/ae874fbd-bd83-474d-b902-afcec142e80b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution {χ : HChar E} {m : ℕ} (hm : 0 < m) (h : χ.OrderDvd m) : IsAlgPos χ 0 := by
  intro k hk
  have h1 : ∀ x, χ.1 x ^ m = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) h
  have h2 : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = algebraMap E w.Completion (k : E) := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have he : e (algebraMap E w.Completion (k : E)) = InfinitePlace.embedding_of_isReal hw (k : E) :=
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm (k : E))
      refine ⟨e.symm ((InfinitePlace.embedding_of_isReal hw (k : E)) ^ ((m : ℝ)⁻¹)), e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply, he, Real.rpow_inv_natCast_pow (hk _).le hm.ne']
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (algebraMap E w.Completion (k : E))) hm
      exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  have h3 : χ.inf k = 1 := by
    show χ.1 (infDiag k) = 1
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    obtain ⟨y, hy⟩ := h2 w
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hy
      exact k.ne_zero hy
    have e : atInf w k = Units.mk0 y hy0 ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy.symm)
    rw [MonoidHom.comp_apply, e, map_pow, map_pow, h1]
  simp [h3]
end GlobalTheory.HeckeGal
