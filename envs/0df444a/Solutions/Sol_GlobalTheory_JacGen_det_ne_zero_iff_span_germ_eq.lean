-- Prove2me | solution 1 for GlobalTheory.JacGen.det_ne_zero_iff_span_germ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:01.494947+00:00
-- url     : https://prove2.me/submissions/12d7afcc-d2a0-4533-a229-b8f643f6a4cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_GlobalTheory_JacGen_det_ne_zero_iff_span_eq
import Theorems.Thm_GlobalTheory_JacGen_isLocalRing_trivSqZeroExt
import Theorems.Thm_GlobalTheory_JacGen_exists_factor
import Theorems.Thm_GlobalTheory_JacGen_exists_derivations
import Theorems.Thm_GlobalTheory_JacGen_valT_specMap_fromSpecStalk
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_lieExp_eq_one
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}
variable [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR K ⟶ G)}
namespace GlobalTheory.JacGen
theorem _root_.solution [LocallyOfFiniteType G.hom] (hv : IsLieBasis v) (z : 𝟙_ _ ⟶ G) (p : Sp K)
    {U : G.left.Opens} (hU : z.left p ∈ U) (f : Fin n → Γ(G.left, U))
    (hf : ∀ i, KeyKa.valT (T := K) z.left U (f i) = 0) :
    (Matrix.of fun i k => (KeyKa.valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v k).left U (f i)).snd).det ≠ 0 ↔
      Ideal.span (Set.range fun i => (G.left.presheaf.germ U _ hU).hom (f i)) =
        maximalIdeal (G.left.presheaf.stalk (z.left p)) := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  letI : Algebra K (G.left.presheaf.stalk (z.left p)) :=
    (Spec.preimage (G.left.fromSpecStalk (z.left p) ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) (G.left.presheaf.stalk (z.left p)) ⟶ G :=
    Over.homMk (G.left.fromSpecStalk (z.left p)) (Spec.map_preimage _).symm
  have : Mono j.left := inferInstanceAs (Mono (G.left.fromSpecStalk (z.left p)))
  have : Mono j := Over.mono_of_mono_left j
  have hpt : ∀ {T : Over (Sp K)} (t : T.left), (toUnit T ≫ z).left t = z.left p := fun {T} t =>
    congrArg z.left (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  obtain ⟨u, hu⟩ := exists_factor j rfl (T := K) (toUnit _ ≫ z) (hpt _)
  have := isLocalRing_trivSqZeroExt (K := K) n
  obtain ⟨χ, hχ⟩ := exists_factor j rfl (T := TrivSqZeroExt K (Fin n → K))
    ((toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) (by
      have h1 : IsLocalHom (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom :=
        ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
      have h2 : spMap (TrivSqZeroExt.fstHom K K (Fin n → K)) ≫ ((toUnit _ ≫ z) * lieExp v
          (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) = toUnit _ ≫ z := by
        rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, ← Category.assoc,
          comp_toUnit]
      rw [← comap_closedPoint (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom, ← hpt (T := sp (R₀ := K) K) (closedPoint K), ← h2]
      rfl)
  obtain ⟨D, h1, h2, h3, h4⟩ := exists_derivations hv j z u hu χ hχ
  have hz : z.left = Spec.map (CommRingCat.ofHom u.toRingHom) ≫ G.left.fromSpecStalk (z.left p) := by
    have h := congrArg (·.left) hu
    have e : (toUnit (sp (R₀ := K) K)).left = 𝟙 (Sp K) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    refine Eq.trans ?_ h.symm
    rw [Over.comp_left, e]
    exact (Category.id_comp _).symm
  rw [← det_ne_zero_iff_span_eq u D h1 h2 h3 _ fun i =>
    (valT_specMap_fromSpecStalk hU _ (f i)).symm.trans ((congrArg (KeyKa.valT (T := K) · U (f i)) hz.symm).trans (hf i))]
  refine iff_of_eq (congrArg (fun M : Matrix (Fin n) (Fin n) K => M.det ≠ 0) (Matrix.ext fun i k => ?_))
  obtain ⟨φ, hφ, hD⟩ := h4 k
  rw [Matrix.of_apply, Matrix.of_apply, ← hD]
  refine congrArg TrivSqZeroExt.snd ?_
  exact (congrArg (fun w : epsR K ⟶ G => KeyKa.valT (T := DualNumber K) w.left U (f i)) hφ.symm).trans
    (valT_specMap_fromSpecStalk hU (CommRingCat.ofHom φ.toRingHom) (f i))
end GlobalTheory.JacGen
