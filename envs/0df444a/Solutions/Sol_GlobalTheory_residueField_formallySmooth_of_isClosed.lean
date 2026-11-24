-- Prove2me | solution 1 for GlobalTheory.residueField_formallySmooth_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:27.800578+00:00
-- url     : https://prove2.me/submissions/e49b9257-2b4e-4e2f-9283-20a5786cc497

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsEtCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldFormallySmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsClosed ({x} : Set X) → letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra; Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  intro k _ _ X f _ U x hxU _
  letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have key : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hS0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType := by
    intro p
    have := StructureSheaf.IsLocalization.to_stalk k p
    have := Algebra.EssFiniteType.of_isLocalization (R := k)
      ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl
    exact RingHom.essFiniteType_algebraMap.mpr this
  have hS : (StructureSheaf.toStalk k (f x)).hom.EssFiniteType := hS0 (f x)
  have hT : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial =
      StructureSheaf.toStalk k (f x) := by
    rw [Scheme.ΓSpecIso_inv]
    exact StructureSheaf.toOpen_germ _ _ _
  have hφ : algebraMap k (X.presheaf.stalk x) =
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial) ≫
        f.stalkMap x).hom := by
    show ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, key]
  have hS' : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Sp k).presheaf.germ ⊤ (f x) trivial).hom.EssFiniteType := hT ▸ hS
  have hR : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have hE : (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))).EssFiniteType := by
    have h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
        (IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x)) := rfl
    rw [h, hφ, CommRingCat.hom_comp]
    exact (hS'.comp (LocallyOfFiniteType.stalkMap f x)).comp hR.essFiniteType
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.essFiniteType_algebraMap.mp hE
  exact Algebra.FormallySmooth.of_perfectField
end GlobalTheory
