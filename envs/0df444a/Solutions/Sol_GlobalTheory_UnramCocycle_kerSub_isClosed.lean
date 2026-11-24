-- Prove2me | solution 1 for GlobalTheory.UnramCocycle.kerSub_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:38.301564+00:00
-- url     : https://prove2.me/submissions/da38a4c1-109f-45f7-baa0-b2c8c7684000

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleUnramifiedOutsideVanishOnKernel
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise
open GlobalTheory GlobalTheory.UnramCocycle
namespace GlobalTheory.UnramCocycle
theorem _root_.solution {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (hρ : ContAction ρ) (x : Z1 ρ) :
    IsClosed (kerSub ρ x : Set Γ) := by

  have h1 : IsClosed {n : Γ | x.1 n = 0} := isClosed_eq x.2.1 continuous_const
  have hc : Continuous fun p : Γ × M => ρ p.1 p.2 := hρ
  have h2 : IsClosed {n : Γ | ∀ m, ρ n m = m} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun m =>
      isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
  exact h1.inter h2
end GlobalTheory.UnramCocycle
