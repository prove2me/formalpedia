-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivJets.bij_of_first_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:54.157574+00:00
-- url     : https://prove2.me/submissions/e0b4eba9-c107-43e8-a135-1c8edcfb723a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_ker_aug_le
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_jet_finite
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_surj_of_first_order
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivJets
variable {V : Type} [CommRing V]
open Chart (JetR zR jetAug_zR jet_ext jetLift jetLift_zR ker_jetAug_pow zR_mem_ker)
namespace GlobalTheory.PowGerm.UnivJets
theorem _root_.solution {σ κ : Type} [Finite σ] {m : ℕ} (β : σ ≃ κ) (f : JetR V σ m →ₐ[V] JetR V κ m)
    (hf : ∀ i, f (zR m i) - zR m (β i) ∈ RingHom.ker (Chart.jetAug V κ m) ^ 2) : Function.Bijective f := by
  refine ⟨?_, surj_of_first_order β β.surjective f hf⟩
  let r : JetR V κ m →ₐ[V] JetR V σ m := jetLift V (RingHom.ker (Chart.jetAug V σ m)) (ker_jetAug_pow σ m)
    (fun k => zR m (β.symm k)) (fun k => zR_mem_ker m _)
  have hr : ∀ k, r (zR m k) = zR m (β.symm k) := fun k => jetLift_zR _ _ _ _ k
  have hle : (RingHom.ker (Chart.jetAug V κ m)).map r ≤ RingHom.ker (Chart.jetAug V σ m) := by
    rw [Ideal.map_le_iff_le_comap]
    refine ker_aug_le fun j => ?_
    rw [Ideal.mem_comap, hr]
    exact zR_mem_ker m _
  have hs : Function.Surjective (r.comp f) := by
    refine surj_of_first_order id Function.surjective_id _ fun i => ?_
    have h1 := Ideal.mem_map_of_mem r (hf i)
    rw [Ideal.map_pow, map_sub, hr, Equiv.symm_apply_apply] at h1
    exact Ideal.pow_right_mono hle 2 h1
  haveI := jet_finite (V := V) σ m
  have hi : Function.Injective (r.comp f) :=
    OrzechProperty.injective_of_surjective_endomorphism (r.comp f).toLinearMap hs
  exact Function.Injective.of_comp (f := r) hi
end GlobalTheory.PowGerm.UnivJets
