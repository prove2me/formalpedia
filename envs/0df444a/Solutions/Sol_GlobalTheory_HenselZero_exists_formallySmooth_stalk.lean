-- Prove2me | solution 1 for GlobalTheory.HenselZero.exists_formallySmooth_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:56:43.369039+00:00
-- url     : https://prove2.me/submissions/54b7d63e-5f1a-4d2e-b8d1-a748f64224dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
namespace GlobalTheory.HenselZero
theorem _root_.solution {O : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec O) [Smooth p] (y : X) :
    ∃ α : O ⟶ X.presheaf.stalk y, α.hom.FormallySmooth ∧ Spec.map α = X.fromSpecStalk y ≫ p := by
  let τ : O ⟶ (Spec O).presheaf.stalk (p y) := StructureSheaf.toStalk O (p y)
  refine ⟨τ ≫ p.stalkMap y, ?_, ?_⟩
  · have hs : (p.stalkMap y).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (p.smoothLocus_eq_top.ge (Set.mem_univ y))
    letI : Algebra O ((Spec O).presheaf.stalk (p y)) := StructureSheaf.stalkAlgebra O (p y)
    have := (p y).isPrime
    have : IsLocalization.AtPrime ((Spec O).presheaf.stalk (p y)) (p y).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk O (p y)
    have h₀ : Algebra.FormallySmooth O ((Spec O).presheaf.stalk (p y)) :=
      Algebra.FormallySmooth.of_isLocalization (p y).asIdeal.primeCompl
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  · have e : (Spec O).fromSpecStalk (p y) = Spec.map τ := Spec.fromSpecStalk_eq' _ _
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, e]
end GlobalTheory.HenselZero
