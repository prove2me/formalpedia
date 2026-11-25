-- Prove2me | solution 1 for GlobalTheory.WachFree.finrank_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:57.198055+00:00
-- url     : https://prove2.me/submissions/f9bde239-2fcb-476b-8431-09a50b94b12a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemXSmulOfProjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open GlobalTheory GlobalTheory.WachFree
namespace GlobalTheory.WachFree
theorem _root_.solution {ι R N : Type} [DecidableEq ι] [CommRing R] [IsLocalRing R] [AddCommGroup N]
    [Module (ι → R) N] [Module.Finite (ι → R) N] [Module.Flat (ι → R) N] (i : ι) :
    ∃ r : ℕ, ∀ (S : Type) [CommRing S] [Nontrivial S] [Algebra (ι → R) S],
      algebraMap (ι → R) S (Pi.single i 1) = 1 → Module.finrank S (S ⊗[ι → R] N) = r := by
  letI : Algebra (ι → R) R := (Pi.evalRingHom (fun _ : ι => R) i).toAlgebra
  haveI : Module.Free R (R ⊗[ι → R] N) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.finrank R (R ⊗[ι → R] N), fun S _ _ _ hS => ?_⟩
  letI : Algebra R S := ((algebraMap (ι → R) S).comp (Pi.constRingHom ι R)).toAlgebra
  haveI : IsScalarTower (ι → R) R S := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap (ι → R) S a = algebraMap (ι → R) S (fun _ => a i)
    have : a * Pi.single i 1 = (fun _ => a i) * Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have h2 := congrArg (algebraMap (ι → R) S) this
    rwa [map_mul, map_mul, hS, mul_one, mul_one] at h2
  rw [← (AlgebraTensorModule.cancelBaseChange (ι → R) R S S N).finrank_eq,
    Module.finrank_baseChange]
end GlobalTheory.WachFree
