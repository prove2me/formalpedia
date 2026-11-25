-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivJets.surj_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:49.961851+00:00
-- url     : https://prove2.me/submissions/5e826e65-7806-4702-a69f-7b02b773710f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_GlobalTheory_SurjectiveOfKerSq_surjective_of_ker_le_map_sup_sq


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
namespace GlobalTheory.PowGerm.UnivJets
theorem _root_.solution {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (aug : B →ₐ[V] V) (m : ℕ) (hI : RingHom.ker aug ^ (m + 1) = ⊥) (J : Ideal A)
    (h1 : J.map f ≤ RingHom.ker aug) (h2 : RingHom.ker aug ≤ J.map f ⊔ RingHom.ker aug ^ 2) :
    Function.Surjective f := by
  first
  | exact @_root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq
  | exact _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq
  | (apply _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq ..)
end GlobalTheory.PowGerm.UnivJets
