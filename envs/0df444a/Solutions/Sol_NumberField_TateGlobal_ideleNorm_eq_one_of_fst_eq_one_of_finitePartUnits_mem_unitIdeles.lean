-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a8ac1193-3946-5d4e-92a9-07551f8d68d1

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField NumberField.AdeleRing

open IsDedekindDomain NumberField.TateGlobal

private theorem norm_le_one_of_mem {F : Type} [Field F] [NumberField F]
    {w : HeightOneSpectrum (𝓞 F)} {x : w.adicCompletion F}
    (hx : x ∈ w.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx)

private theorem norm_one_apply_pow_mult (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) : ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1 := by
  rw [show (1 : InfiniteAdeleRing F) w = 1 from rfl, norm_one, one_pow]

private theorem norm_snd_apply_eq_one {F : Type} [Field F] [NumberField F]
    (u : (AdeleRing (𝓞 F) F)ˣ)
    (hfin : finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F)
    (w : HeightOneSpectrum (𝓞 F)) : ‖(u : AdeleRing (𝓞 F) F).2 w‖ = 1 := by
  obtain ⟨h1, h2⟩ := (IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff _).mp hfin
  have ha : ‖(u : AdeleRing (𝓞 F) F).2 w‖ ≤ 1 := norm_le_one_of_mem (h1 w)
  have hb : ‖((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w‖ ≤ 1 :=
    norm_le_one_of_mem (h2 w)
  have hab : (u : AdeleRing (𝓞 F) F).2 w * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
      = 1 :=
    congrArg (fun x : AdeleRing (𝓞 F) F => x.2 w) u.mul_inv
  have hmul := norm_mul ((u : AdeleRing (𝓞 F) F).2 w)
    (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w)
  rw [hab, norm_one] at hmul
  have hge := mul_le_mul_of_nonneg_left hb (norm_nonneg ((u : AdeleRing (𝓞 F) F).2 w))
  exact le_antisymm ha (by linarith)

theorem solution (F : Type) [Field F] [NumberField F] (u : (AdeleRing (𝓞 F) F)ˣ)
    (harch : (u : AdeleRing (𝓞 F) F).1 = 1)
    (hfin : finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F) :
    ideleNorm F u = 1 := by
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, harch,
    Finset.prod_eq_one (fun w _ => norm_one_apply_pow_mult F w), one_mul]
  exact finprod_eq_one_of_forall_eq_one (norm_snd_apply_eq_one u hfin)

end S_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles (solution)
