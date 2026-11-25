-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.smul_basis_mem_hat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:07.269553+00:00
-- url     : https://prove2.me/submissions/606f07c6-b1bb-4eeb-8854-3422eb90d7c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Theorems.Thm_GlobalTheory_AdLat_Model_functional_integral
import Theorems.Thm_GlobalTheory_AdLat_Model_fv_mem_hat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
theorem _root_.solution {n : ℕ} {ι : Type} (b : Module.Basis ι F (Fin n → E)) (j : ι) (t : F) :
    fv F (t • b j) ∈ hat F (freeLat b) ↔ t ∈ (algebraMap (𝓞 F) F).range := by
  classical
  constructor
  · intro h
    simpa using functional_integral (freeLat b) (b.coord j) (fun x hx => hx j) h
  · intro ht
    refine fv_mem_hat fun k => ?_
    by_cases hk : j = k
    · subst hk; simpa using ht
    · simp only [Module.Basis.coord_apply, map_smul, Module.Basis.repr_self, smul_eq_mul,
        Finsupp.single_eq_of_ne (Ne.symm hk), mul_zero]
      exact zero_mem _
end GlobalTheory.AdLat.Model
