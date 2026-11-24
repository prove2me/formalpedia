-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.tmul_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:22.580356+00:00
-- url     : https://prove2.me/submissions/84e23d07-c2f3-4dfe-a4d5-47830ce8b8eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_fixed_integral
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_exists_incl
import Theorems.Thm_GlobalTheory_AdLat_adele_mul_integral
import Theorems.Thm_GlobalTheory_AdLat_mem_range_iff_adele_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable (F : Type) [Field F] [NumberField F]
variable (E : Type) [Field E] [NumberField E] [Algebra F E]
variable {F E}
namespace GlobalTheory.AdLat.UnitRoot
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E}
    (hx : x ∈ Set.range (algebraMap (𝓞 E) E)) (hfix : c x = x) :
    ∃ b, (a ⊗ₜ[F] x : RA F E) = incl F b ⊗ₜ[F] 1 := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, hy, hyx⟩ := fixed_integral c h2 hc _ (RingOfIntegers.isIntegral_coe x) hfix
  obtain ⟨b, hb⟩ := exists_incl F (a := algebraMap F _ y * a)
    (fun v => adele_mul_integral F ((mem_range_iff_adele_integral F y).1 hy v) (ha v))
  refine ⟨b, ?_⟩
  rw [hb, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hyx]
end GlobalTheory.AdLat.UnitRoot
