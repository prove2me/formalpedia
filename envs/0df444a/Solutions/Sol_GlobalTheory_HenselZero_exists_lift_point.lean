-- Prove2me | solution 1 for GlobalTheory.HenselZero.exists_lift_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:54.280847+00:00
-- url     : https://prove2.me/submissions/9b50f7a5-935b-4c73-8ba0-f214053d3cd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TransversalZerosLiftOfIsAdicComplete
import Theorems.Thm_GlobalTheory_HenselZero_exists_gs_via
import Theorems.Thm_GlobalTheory_HenselZero_exists_section_of_transversal
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_fst_comp_translate
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_fst_valT_translate
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_le_inf_pull
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_snd_map
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_snd_pow_mul
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_translate_comp
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_translate_le
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_eq
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_spMap
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_via
import Theorems.Thm_GlobalTheory_KeyKa_jac_ne_zero_iff_span_eq_maximalIdeal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
open GlobalTheory.KeyKa.EtBaseChange
namespace GlobalTheory.HenselZero
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {x : KeyIn O} {xk : KeyIn (IsLocalRing.ResidueField O)} {φ w}
    {n : ℕ} (hg : xk.P.g = x.P.g) {s : Fin x.P.g → RR x n} {sk : Fin xk.P.g → RR xk n}
    (hvia : KeyVia xk x (IsLocalRing.residue O) φ w) (hs : ∀ i, SecVia xk x φ w (sk i) (s (i.cast hg)))
    (zk : Pt xk) (c' : xk.P.L.ι) (h₁ : ⊤ ≤ zk.left ⁻¹ᵁ xk.P.L.U c')
    (h₂ : ∀ i, valT (T := IsLocalRing.ResidueField O) zk.left (xk.P.L.U c') ((sk i).f c') = 0)
    (h₃ : IsUnit (jac xk sk zk c')) :
    ∃ (z : Pt x) (c : x.P.L.ι), spMap (IsLocalRing.residue O) ≫ z.left = zk.left ≫ φ ∧ ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧
      (∀ i, valT (T := O) z.left (x.P.L.U c) ((s i).f c) = 0) ∧ IsUnit (jac x s z c) ∧
      ∀ (y : x.P.A.left) (pt : Sp (IsLocalRing.ResidueField O)), y ⤳ φ (zk.left pt) →
        (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ r : Sp O, z.left r = y := by
  obtain ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ := hvia
  have := x.P.isAb.smooth
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hpt : ∀ r : Sp (IsLocalRing.ResidueField O), r = pt := fun r =>
    Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField O)) _ _
  obtain ⟨c, hc⟩ := exists_chart x.P.isLB (φ (zk.left pt))
  have hc' : zk.left pt ∈ xk.P.L.U c' := h₁ (x := pt) trivial
  have hφ : ⊤ ≤ (zk.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun r _ => by
    obtain rfl := hpt r
    exact hc
  have hW := le_inf_pull (T := IsLocalRing.ResidueField O) zk.left c c' hφ h₁
  let u := Units.map (valH (T := IsLocalRing.ResidueField O) zk.left _ hW).toMonoidHom (w.s (fun _ => c, c'))
  have hu : valT (T := IsLocalRing.ResidueField O) zk.left ((x.P.L.pull φ).U (fun _ => c) ⊓ xk.P.L.U c')
      (w.s (fun _ => c, c')).val = u := valT_eq _ _ hW _
  have hd : (Matrix.of fun i k => (valT (T := DualNumber (IsLocalRing.ResidueField O))
      (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) (x.P.L.U c) ((s (i.cast hg)).f c)).snd).det ≠ 0 := by
    refine fun h => mul_ne_zero (pow_ne_zero (Fintype.card (Fin xk.P.g)) (pow_ne_zero n u.ne_zero)) h₃.ne_zero
      ((Matrix.det_smul _ _).symm.trans (Eq.trans ?_ h))
    congr 1
    ext i k
    have l₂ := translate_le zk (xk.v k) (xk.basis.1 _) h₁
    have l₃ : ⊤ ≤ (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U c :=
      translate_le zk (xk.v k) (xk.basis.1 _) (U := φ ⁻¹ᵁ x.P.L.U c) hφ
    have e := valT_via (T := DualNumber (IsLocalRing.ResidueField O)) (hs i) _ c c' l₃ l₂
    refine Eq.symm ((congrArg TrivSqZeroExt.snd e).trans ?_)
    refine (snd_pow_mul _ _ _ ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) h₁ _).trans (h₂ i))).trans ?_
    exact congrArg (· ^ n * _) ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) hW _).trans hu)
  obtain ⟨z₀, hz₁, hz₂, hz₃, hz₄⟩ := exists_section_of_transversal hp.1 zk.left (Over.w zk) pt hc
    (fun i : Fin xk.P.g => (s (i.cast hg)).f c)
    (fun i => (valT_via (T := IsLocalRing.ResidueField O) (hs i) zk.left c c' hφ h₁).trans
      (mul_eq_zero_of_right _ (h₂ i)))
    (by
      rw [← (jac_ne_zero_iff_span_eq_maximalIdeal _ xk n sk zk c' pt h₁ h₂).1 h₃.ne_zero]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨v, hv, e⟩ := exists_gs_via (hs i) (zk.left pt) c c' hc hc'
      exact (Ideal.unit_mul_mem_iff_mem _ hv).1 (Ideal.subset_span ⟨i, e⟩))
    (fun k => ((toUnit (epsR _) ≫ zk) * xk.v k).left)
    (fun k => fst_comp_translate zk (xk.v k) (xk.basis.1 _)) (fun k => Over.w ((toUnit (epsR _) ≫ zk) * xk.v k)) hd
  let z : Pt x := Over.homMk z₀ hz₁
  have hz : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := (Scheme.preimage_eq_top_of_closedPoint_mem z₀ (by
    rw [← IsLocalRing.comap_closedPoint (IsLocalRing.residue O)]
    exact (congrArg (fun g => g pt ∈ x.P.L.U c) hz₂).ge hc)).ge
  refine ⟨z, c, hz₂, hz, fun i => hz₃ (i.cast hg.symm), ?_, fun y r hy hy' => ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    refine fun h => hd (Eq.trans ?_ h)
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg)]
    congr 1
    ext i k
    have e := translate_comp hp F hF₁ z zk hz₂.symm (x.v (k.cast hg)) (xk.v k) (hv k)
    have l₁ := translate_le z (x.v (k.cast hg)) (x.basis.1 _) hz
    have e₂ := (congrArg (fun q => valT (T := DualNumber (IsLocalRing.ResidueField O)) q (x.P.L.U c)
      ((s (i.cast hg)).f c)) e).trans (valT_spMap F _ l₁ _)
    exact (congrArg TrivSqZeroExt.snd e₂).trans (snd_map _ F hF₁ hF₂ _)
  · obtain rfl := hpt r
    exact hz₄ y hy fun i h => hy' (i.cast hg) (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)
end GlobalTheory.HenselZero
