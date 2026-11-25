-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.UnitBall.isDVR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:17:16.323068+00:00
-- url     : https://prove2.me/submissions/b83b48b3-72d2-4339-a625-e6375eafa4cf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_isUnit_of_norm_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_norm_unif_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_exists_nat_norm
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_unif_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_irreducible_unif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.UnitBall
variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
variable {L}
variable {p : Lˣ}
namespace GlobalTheory.CompanionTheory.CartGL.UnitBall
theorem _root_.solution (hp : IsUnif p) : IsDiscreteValuationRing (ball L) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif hp, irreducible_unif hp, ?_⟩
  intro x hx
  have hx0 : (x : L) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨m, hm⟩ := exists_nat_norm hp hx0 x.2
  have h0 := norm_unif_pos p
  have hpm : (p : L) ^ m ≠ 0 := pow_ne_zero _ p.ne_zero
  have hq : ‖(x : L) / (p : L) ^ m‖ = 1 := by
    rw [norm_div, norm_pow, hm]
    exact div_self (pow_ne_zero _ h0.ne')
  let q : ball L := ⟨(x : L) / (p : L) ^ m, hq.le⟩
  obtain ⟨u, hu⟩ := isUnit_of_norm_eq_one (x := q) hq
  refine ⟨m, u, ?_⟩
  apply Subtype.ext
  have hu' : ((u : ball L) : L) = (x : L) / (p : L) ^ m := by rw [hu]
  change ((unif hp : ball L) : L) ^ m * ((u : ball L) : L) = (x : L)
  rw [hu', unif_coe]
  field_simp
end GlobalTheory.CompanionTheory.CartGL.UnitBall
