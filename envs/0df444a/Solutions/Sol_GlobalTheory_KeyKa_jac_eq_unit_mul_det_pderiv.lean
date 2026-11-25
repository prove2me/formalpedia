-- Prove2me | solution 1 for GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:47.831371+00:00
-- url     : https://prove2.me/submissions/1eeca93f-e667-42c0-ac00-fc7542daca80

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacEqUnitMulDetPderiv
import Theorems.Thm_GlobalTheory_JacSer_isLocalRing_trivSqZeroExt
import Theorems.Thm_GlobalTheory_JacSer_isLocalHom_of_X_mem
import Theorems.Thm_GlobalTheory_JacSer_exists_matrix
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_isAdicComplete_maximalIdeal_of_finite
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_spMap
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_lieExp_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (θ : Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left) (z : Pt x) (e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] O), θ ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O)) → (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) θ V (t i) = MvPowerSeries.X i) → (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ x.P.A.left), w ≫ x.P.A.hom = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) → ∃ e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) → (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → spMap e.toRingHom ≫ θ = z.left → ∃ u : Oˣ, ∀ (n : ℕ) (s : Fin x.P.g → RR x n) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → jac x s z c = u * e (Matrix.of fun i j => MvPowerSeries.pderiv O j (valT (T := (MvPowerSeries (Fin x.P.g) O)) θ (x.P.L.U c) ((s i).f c))).det := by
  intro O _ _ _ _ x θ z e hθ ⟨V, t, hV, ht⟩ hlift he hz
  let j : Chart.sp (R₀ := O) (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A := Over.homMk θ hθ
  have hloc := GlobalTheory.JacSer.isLocalHom_of_X_mem e he
  have hcl : z.left (IsLocalRing.closedPoint O) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) := by
    rw [← hz, ← IsLocalRing.comap_closedPoint e.toRingHom]
    rfl
  have hu : Chart.spMap e ≫ j = toUnit _ ≫ z := by
    apply Over.OverMorphism.ext
    have e1 : (toUnit (Chart.sp (R₀ := O) O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    rw [Over.comp_left, Over.comp_left, e1]
    exact hz.trans (Category.id_comp _).symm
  have := GlobalTheory.JacSer.isLocalRing_trivSqZeroExt (O := O) (Fin x.P.g → O)
  have : Module.Finite O (TrivSqZeroExt O (Fin x.P.g → O)) :=
    inferInstanceAs (Module.Finite O (O × (Fin x.P.g → O)))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (TrivSqZeroExt O (Fin x.P.g → O))
  let w : Chart.sp (R₀ := O) (TrivSqZeroExt O (Fin x.P.g → O)) ⟶ x.P.A :=
    (toUnit _ ≫ z) * GlobalTheory.SqZero.lieExp x.v (fun i => TrivSqZeroExt.inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  obtain ⟨χ, -, hχ⟩ := hlift (TrivSqZeroExt O (Fin x.P.g → O)) w.left (Over.w w) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    have h2 : Chart.spMap (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)) ≫ w = Chart.spMap e ≫ j := by
      rw [hu, MonObj.comp_mul, GlobalTheory.SqZero.comp_lieExp, GlobalTheory.SqZero.lieExp_eq_one x.basis.1 _ (fun i => by rfl),
        _root_.mul_one, ← Category.assoc, comp_toUnit]
    have h3 := congrArg (fun q => q.left (IsLocalRing.closedPoint O)) h2
    rw [← IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom,
      ← IsLocalRing.comap_closedPoint e.toRingHom]
    exact h3)
  obtain ⟨C, hC, hφ⟩ := GlobalTheory.JacSer.exists_matrix x.basis j (fun φ ψ h i => by
    have h1 : spMap φ.toRingHom ≫ θ = spMap ψ.toRingHom ≫ θ := congrArg (·.left) h
    have h2 := EtBaseChange.valT_spMap φ.toRingHom θ hV (t i)
    rw [h1, EtBaseChange.valT_spMap ψ.toRingHom θ hV, ht] at h2
    exact h2.symm) z e he hu χ (Over.OverMorphism.ext hχ)
  refine ⟨hC.unit, fun n s c hc => ?_⟩
  have hθc : ⊤ ≤ θ ⁻¹ᵁ x.P.L.U c := fun p _ =>
    ((IsLocalRing.specializes_closedPoint p).map θ.continuous).mem_open (x.P.L.U c).isOpen
      (hcl ▸ hc (x := IsLocalRing.closedPoint O) trivial)
  rw [IsUnit.unit_spec, _root_.mul_comm, AlgHom.map_det, ← Matrix.det_mul]
  refine congrArg Matrix.det (Matrix.ext fun i k => ?_)
  obtain ⟨φ, h1, h2⟩ := hφ k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine Eq.trans (congrArg TrivSqZeroExt.snd ?_) (h2 _)
  exact (congrArg (fun q : epsR O ⟶ x.P.A => valT (T := DualNumber O) q.left (x.P.L.U c) ((s i).f c)) h1.symm).trans
    (EtBaseChange.valT_spMap φ.toRingHom θ hθc _)
end GlobalTheory.KeyKa
