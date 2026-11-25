-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivJets.surj_of_first_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:24.452343+00:00
-- url     : https://prove2.me/submissions/5d00893b-8891-4c1c-ace7-6937c6a293e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_surj_of_sq
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_ker_aug_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker


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
theorem _root_.solution {σ κ : Type} {m : ℕ} (β : σ → κ) (hβ : Function.Surjective β)
    (f : JetR V σ m →ₐ[V] JetR V κ m)
    (hf : ∀ i, f (zR m i) - zR m (β i) ∈ RingHom.ker (Chart.jetAug V κ m) ^ 2) : Function.Surjective f := by
  refine surj_of_sq f (Chart.jetAug V κ m) m (ker_jetAug_pow κ m) (Ideal.span (Set.range (zR m))) ?_ ?_
  · rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have := Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero (hf i)) (zR_mem_ker (R := V) m (β i))
    rwa [sub_add_cancel] at this
  · refine ker_aug_le fun j => ?_
    obtain ⟨i, rfl⟩ := hβ j
    have h1 : f (zR m i) ∈ (Ideal.span (Set.range (zR (R := V) (κ := σ) m))).map f :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    have := Ideal.sub_mem _ (Ideal.mem_sup_left (T := RingHom.ker (Chart.jetAug V κ m) ^ 2) h1)
      (Ideal.mem_sup_right (hf i))
    rwa [sub_sub_cancel] at this
end GlobalTheory.PowGerm.UnivJets
