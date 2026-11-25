-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.mem_intAE_of_mem_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:40.87695+00:00
-- url     : https://prove2.me/submissions/3b00d7eb-9bc5-491a-86dd-33b7534a0e0c

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finEquiv_one_tmul
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finEquiv_symm_eq_sum
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_algebraMap_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_exists_basis_isIntegral
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_mem_integralFiniteAdeles_mul_of_isIntegral
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_localCoord_mem
import Theorems.Thm_GroundTheory_Global_coe_mem_adicCompletionIntegers_iff
import Theorems.Thm_GroundTheory_Global_exists_sub_mem_integralFiniteAdeles


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution {t : FiniteAdeleRing (𝓞 E) E}
    (ht : t ∈ integralFiniteAdeles (𝓞 E) E) : (finEquiv F E).symm t ∈ intAE F E := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_isIntegral (F := F) (E := E)
  obtain ⟨D, hD0, hD⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image (traceDual b))

  have hcoord : ∀ s ∈ integralFiniteAdeles (𝓞 E) E,
      (finEquiv F E).symm ((D : FiniteAdeleRing (𝓞 E) E) * s) ∈ intAE F E := by
    intro s hs
    rw [finEquiv_symm_eq_sum b]
    refine AddSubgroup.sum_mem _ fun i _ ↦ AddSubgroup.subset_closure
      ⟨finiteCoord b i ((D : FiniteAdeleRing (𝓞 E) E) * s), fun v ↦ ?_, ⟨b i, hb i⟩, rfl⟩
    change localCoord b v i _ ∈ _
    refine localCoord_mem b v i _ fun w ↦ ?_
    have h := mem_integralFiniteAdeles_mul_of_isIntegral hs
      (hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) w.1
    have he : ((D : FiniteAdeleRing (𝓞 E) E) * s) w.1 * algebraMap E (w.1.adicCompletion E) (traceDual b i)
        = s w.1 * algebraMap E (w.1.adicCompletion E) (D • traceDual b i) := by
      rw [zsmul_eq_mul, map_mul, map_intCast]
      change ((D : w.1.adicCompletion E) * s w.1) * _ = _
      ring
    rw [he]
    exact h

  have hDE : (D : E) ≠ 0 := Int.cast_ne_zero.2 hD0
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 E) (K := E)
    (t * algebraMap E (FiniteAdeleRing (𝓞 E) E) (D : E)⁻¹)
  set s := t * algebraMap E (FiniteAdeleRing (𝓞 E) E) (D : E)⁻¹ - algebraMap E _ k with hs
  have hDc : (D : FiniteAdeleRing (𝓞 E) E) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (D : E) := by
    rw [map_intCast]
  have htk : t = algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k) +
      (D : FiniteAdeleRing (𝓞 E) E) * s := by
    rw [hs, hDc, mul_sub, ← mul_assoc, mul_comm (algebraMap E _ (D : E)) t, mul_assoc, ← map_mul,
      mul_inv_cancel₀ hDE, map_one, mul_one, map_mul]
    ring
  have hDk : (D : E) * k ∈ (algebraMap (𝓞 E) E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (K := E) _ fun w ↦ ?_
    rw [← coe_mem_adicCompletionIntegers_iff]
    have h1 : algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k) ∈ integralFiniteAdeles (𝓞 E) E := by
      have h2 : algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k) =
          t - (D : FiniteAdeleRing (𝓞 E) E) * s := by
        rw [htk]; ring
      rw [h2]
      refine Subring.sub_mem _ ht (Subring.mul_mem _ ?_ hk)
      rw [hDc]
      exact algebraMap_mem_integralFiniteAdeles (D : 𝓞 E)
    exact h1 w
  obtain ⟨z, hz⟩ := hDk
  rw [htk, map_add]
  refine AddSubgroup.add_mem _ ?_ (hcoord s hk)
  have h1 : (finEquiv F E).symm (algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k)) =
      (1 : Af F) ⊗ₜ[F] ((z : 𝓞 E) : E) := by
    rw [RingEquiv.symm_apply_eq, finEquiv_one_tmul, ← hz]
  rw [h1]
  exact AddSubgroup.subset_closure ⟨1, fun v ↦ Subring.one_mem _, z, rfl⟩
end GroundTheory.BlockD.ThmBHecke
